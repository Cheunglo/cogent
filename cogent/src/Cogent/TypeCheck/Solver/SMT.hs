--
-- Copyright 2019, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

{-# LANGUAGE LambdaCase #-}

module Cogent.TypeCheck.Solver.SMT where

import Cogent.Compiler
import Cogent.Common.Syntax
import Cogent.TypeCheck.Base as Tc
import Cogent.TypeCheck.SMT
import Cogent.TypeCheck.Solver.Goal
import Cogent.TypeCheck.Solver.Monad (TcSolvM)
import Cogent.TypeCheck.Solver.Rewrite as Rewrite hiding (lift)
import Cogent.TypeCheck.Util (traceTc)
import Cogent.PrettyPrint (indent', warn)
import Cogent.Surface
import Cogent.Util (hoistMaybe, (.>))

import Control.Monad.IO.Class
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.RWS (RWST (..))
import qualified Data.IntMap as IM (empty)
import qualified Data.Map as M (Map, empty, map, toList)
import Data.Maybe (fromMaybe)
import Data.SBV (AllSatResult (..), SatResult (..), ThmResult (..), SMTResult (..), z3)
import Data.SBV.Dynamic (allSatWith, satWith, proveWith, SMTConfig (..))
import Lens.Micro
import Lens.Micro.Mtl (view)
import qualified Text.PrettyPrint.ANSI.Leijen as L

import Debug.Trace

data SmtState = SmtState { constraints :: [TCSExpr] }

type SmtM = StateT SmtState TcSolvM

-- | Top-level rewrite function for solving constraints using an SMT-solver.
smt :: RewriteT TcSolvM [Goal]
smt = trans $ smtSolve

-- | Transforms a 'RewriteT SmtM a' computation to a 'RewriteT TcSolvM a' computation.:
trans :: RewriteT SmtM a -> RewriteT TcSolvM a
trans (RewriteT m) = RewriteT $ \a ->
  let MaybeT (StateT m') = m a
   in MaybeT $ fst <$> m' (SmtState [])

-- | Extracts all logical predicates from goals and then,
--   simplifies them using the knowledge of constant definitions.
smtSolve :: RewriteT SmtM [Goal]
smtSolve = 
  extractPredicates `andThen`
  (rewrite' $ \gs -> do
    ks <- M.map (\(a,b,c) -> (a,b)) <$> view knownConsts
    SmtState c <- get
    let ks' = constEquations ks
    traceTc "sol/smt" (L.text "Constants" L.<> L.colon L.<$> L.prettyList ks')
    res <- liftIO $ smtSatResult $ implTCSExpr (andTCSExprs ks') (andTCSExprs c)
    case res of (_ , _, []) -> hoistMaybe $ Nothing   -- returns no models
                (False, False, [m]) -> hoistMaybe $ Just gs  -- TODO: only one model, we should generate assignment
                (_, _, ms) -> hoistMaybe $ Just gs  -- TODO: multiple models. check if the unifs are
                                                    -- the only occurrences. if so, then generate assignment.
   )

-- | Converts the store of known constants to equality constraints.
constEquations :: M.Map VarName (TCType, TCExpr) -> [TCSExpr]
constEquations = M.toList .>
                 filter simpleExpr .>
                 map (\(v,(t,e)) -> SE (T bool) (PrimOp "==" [SE t (Var v), toTCSExpr e]))
  where simpleExpr (_,(_,e)) = simpleTE e

-- | Finds and stores in 'StmM' all logical predicates from constraints, and remove them
--   from the 'SolvM' store.
extractPredicates :: RewriteT SmtM [Goal]
extractPredicates = pickOne' $ \g -> do
  let c = g ^. goal
      (es,c') = splitArithConstraints c
  if null es then
    hoistMaybe $ Nothing
  else do
    modify (\(SmtState es') -> SmtState (es'++es))
    hoistMaybe $ Just [g & goal .~ c']

-- | Returns a detailed result of satisfiability of a logical predicate.
smtSatResult :: TCSExpr -> IO (Bool, Bool, [SMTResult])
smtSatResult e = do
  dumpMsgIfTrue __cogent_ddump_smt (warn "SMT solving:" L.<+> L.pretty e L.<> L.hardline)
  -- NOTE: sbv will perform Skolemisation to reduce existentials, while preserving satisfiability. / zilinc
  res@(AllSatResult (limit, _, unknown, models)) <-
    allSatWith (z3 { verbose = __cogent_ddump_smt
                   , redirectVerbose = Just $ fromMaybe "/dev/stderr" __cogent_ddump_to_file })
               (evalStateT (sexprToSmt e)
               (SmtTransState IM.empty M.empty))
  dumpMsgIfTrue __cogent_ddump_smt (L.text (replicate 80 '-') L.<> L.hardline)
  traceTc "sol/smt" (L.text "Running SMT on expression"
                     L.<$> indent' (L.pretty e)
                     L.<$> L.text "gives result"
                     L.<$> indent' (L.text $ show res))
  return (limit, unknown, models)

-- | Only returns 'True' or 'False'.
smtSat :: TCSExpr -> IO Bool
smtSat e = 
  smtSatResult e >>= \case
    (_, False, models) | length models > 0 -> return True
    _ -> return False
