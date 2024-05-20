--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module Cogent.TypeCheck.Solver.Goal where

import qualified Data.IntMap as IM
import           Cogent.TypeCheck.Base
import           Cogent.PrettyPrint
--import qualified Text.PrettyPrint.ANSI.Leijen as P
--import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>), (<>))
import           Prettyprinter hiding ((<>))
import           Isabelle.PrettyAnsi
import qualified Data.Foldable as F
import           Lens.Micro
import           Lens.Micro.TH

-- A more efficient implementation would be a term net

data Goal = Goal { _goalContext :: [ErrorContext]
                 , _goal :: Constraint
                 }  -- high-level context at the end of _goalContext

instance Show Goal where
  show (Goal c g) = show big
    where big = (small `vsep2` (vcat $ map (`prettyCtx` True) c))
          small = ansiP g

makeLenses ''Goal

makeGoals :: [ErrorContext] -> Constraint -> [Goal]
makeGoals ctx (constraint :@ c) = makeGoals (c:ctx) constraint
makeGoals ctx (c1 :& c2) = makeGoals ctx c1 ++ makeGoals ctx c2
makeGoals ctx g = pure $ Goal ctx g

makeGoal :: [ErrorContext] -> Constraint -> Goal
makeGoal ctx (constraint :@ c) = makeGoal (c:ctx) constraint
makeGoal ctx g = Goal ctx g

derivedGoal :: Goal -> Constraint -> Goal
derivedGoal (Goal c g) g' = makeGoal (SolvingConstraint g:c) g'

getMentions :: [Goal] -> IM.IntMap (Int,Int)
getMentions gs =
  foldl (IM.unionWith adds) IM.empty $ fmap mentionsOfGoal gs
  where
    adds (a,b) (c,d) = (a + c, b + d)

    mentionsOfGoal g = case g ^. goal of
      r :< s -> IM.fromListWith adds (mentionL r ++ mentionR s)
      _      -> IM.empty

    mentionL = fmap (\v -> (v, (1,0))) . unifVars
    mentionR = fmap (\v -> (v, (0,1))) . unifVars
