

-- |
-- Module      : Minigent.Termination2
-- Copyright   : (c) Data61 2018-2019
--                   Commonwealth Science and Research Organisation (CSIRO)
--                   ABN 41 687 119 230
-- License     : BSD3
--
-- The termination checking module
--
-- May be used qualified or unqualified.
module Minigent.Termination

  ( termCheck
  , genGraphDotFile
  , Assertion (..) 
  ) where

import Minigent.Fresh
import Minigent.Syntax
import Minigent.Syntax.Utils
import Minigent.Environment
import Minigent.Syntax.PrettyPrint

import Control.Monad.State.Strict
import Data.Maybe (maybeToList, catMaybes)

import qualified Data.Map as M
import qualified Data.Set as S
import Data.List

data AST
  = RecordAST String AST 
  | RecursiveRecordAST String String AST 
  | RecParAST String
  | VariantAST String AST 
  | IntAST
  | BoolAST 
  | UnitAST 
  | AbsTypeAST 
  | TypeVarAST 
  | FunctionAST
  | ErrorAST
  deriving (Show, Eq)

  -- | A type, which may contain unification variables or type operators.
-- data Type
--   = PrimType PrimType
--   | Record RecPar Row Sigil -- ^ A recursive parameter, field entry row and sigil
--   | AbsType AbsTypeName Sigil [Type]
--   | Variant Row
--   | TypeVar VarName -- ^ Refers to a rigid type variable bound with a forall.
--   | TypeVarBang VarName -- ^ A 'TypeVar' with 'Bang' applied.
--   -- ^ Refers to a recursive parameter, with the context of it's recursive references for Unrolling
--   | RecPar VarName RecContext     -- ^ A recursive parameter.
--   | RecParBang VarName RecContext -- ^ A 'RecPar' with 'Bang' applied.
--   | Function Type Type
--   -- used in type inference:
--   | UnifVar VarName -- ^ Stands for an unknown type
--   | Bang Type -- ^ Eliminated by type normalisation.
--   deriving (Show, Eq)

buildMeasure :: Type -> [AST] -> [AST]
buildMeasure t res = 
  case t of 
    PrimType p -> 
      case p of 
        Unit -> UnitAST:res
        Bool -> BoolAST:res
        _    -> IntAST:res
    Record recpar row sig -> parseRecord recpar $ M.toList (rowEntries row)
    Variant row -> parseVariant $ M.toList (rowEntries row)
    RecPar t rc -> RecParAST t : res
    RecParBang t rc -> RecParAST t : res
    AbsType name sig ty -> AbsTypeAST : res
    TypeVar v -> TypeVarAST : res
    TypeVarBang v -> TypeVarAST : res
    UnifVar v -> TypeVarAST : res -- ? need more?
    Function x y -> FunctionAST : res
    Bang t -> buildMeasure t []

parseRecord :: RecPar -> [(FieldName, Entry)] -> [AST]
parseRecord _ [] = []
parseRecord recpar ((f, Entry _ ty _): rs) = 
  let children = buildMeasure ty []
      rest = parseRecord recpar rs
  in case recpar of 
    None -> (map (\x -> RecordAST f x) children) ++ rest
    Rec recpar' -> (map (\x -> RecursiveRecordAST recpar' f x) children) ++ rest
    UnknownParameter t -> [] -- shouldn't happen, should be caught by type checker

parseVariant :: [(FieldName, Entry)] -> [AST]
parseVariant [] = []
parseVariant ((f, Entry _ ty _): rs) = 
  let children = buildMeasure ty []
  in (map (\x -> VariantAST f x) children) ++ (parseVariant rs)

-- A directed graph maps a node name to all reachable nodes from that node
type Node  = String
type Graph = M.Map Node [Node]

-- Our environment, a mapping between program variables and fresh variables
type FreshVar = String
type Env = M.Map VarName FreshVar

type Error    = String
type DotGraph = String

getMeasure :: FunName -> GlobalEnvironments -> Maybe [AST]
getMeasure f genvs = 
  case M.lookup f (types genvs) of 
    Nothing -> Nothing 
    Just (Forall _ _ ty) -> 
      case ty of 
        Function x y -> Just (buildMeasure x [])
        _ -> Nothing 

termCheck :: GlobalEnvironments -> ([Error], [(FunName, [Assertion], String)])
termCheck genvs = M.foldrWithKey go ([],[]) (defns genvs)
  where
    go :: FunName -> (VarName, Expr) -> ([Error], [(FunName, [Assertion], DotGraph)]) -> ([Error], [(FunName, [Assertion], DotGraph)])
    go f (x,e) (errs, dumps) =  
      let measure = getMeasure f genvs
          (terminates, g, dotGraph) = fst $ runFresh unifVars (init f x e)
          errs' = if terminates then
                    (show measure ++ " ---- ") :errs
                  else
                    (show measure ++ " ---- " ++ "Error: Function " ++ f ++ " cannot be shown to terminate.") : errs
        in 
          (errs', (f, g, dotGraph) : dumps)

    -- Maps the function argument to a name, then runs the termination
    -- assertion generator.
    -- Returns: 
    --  ( true if the function terminates
    --  , the list of assertions produced from the function
    --  , the `dot' graph file for this particular termination graph
    --  )
    init :: FunName -> VarName -> Expr -> Fresh VarName (Bool, [Assertion], String)
    init f x e = do
      alpha <- fresh
      let env = M.insert x alpha M.empty
      (a,c) <- termAssertionGen env e

      let graph = toGraph a
      let goals = catMaybes c

      -- If all goals are not nothing, and our path condition is met, then the function terminates
      -- Otherwise, we cannot say anything about the function
      let terminates = length goals == length c 
                    && all (\goal -> hasPathTo alpha goal graph
                                  && (not $ hasPathTo goal alpha graph)
                           ) goals
      return $ 
        (
          terminates,
          a,
          genGraphDotFile f graph [alpha] goals
        )

termAssertionGen ::  Env -> Expr -> Fresh VarName ([Assertion], [Maybe FreshVar])
termAssertionGen env expr
  = case expr of
    PrimOp _ es ->
      join $ map (termAssertionGen env) es
      
    Sig e _ -> 
      termAssertionGen env e

    Apply f e -> do
      a <- termAssertionGen env f
      b <- termAssertionGen env e
      return $ flatten [([], [getv env e]), a, b]
      
    Struct fs ->
      let es = map snd fs 
      in join $ map (termAssertionGen env) es
      
    If b e1 e2 ->
      join $ map (termAssertionGen env) [b, e1, e2]
      
    Let x e1 e2 -> do
      -- First evaluate the variable binding expression
      a <- termAssertionGen env e1

      -- Map our bound program variable to a new name and evaluate the rest
      alpha <- fresh
      let env' = M.insert x alpha env 
      res <- termAssertionGen env' e2

      -- Generate assertion
      let l = toAssertion env e1 (alpha :~:)
      return $ flatten [(l,[]), res]
    
    LetBang vs v e1 e2 ->
      termAssertionGen env (Let v e1 e2)

    Take r' f x e1 e2 -> do
      alpha <- fresh 
      beta  <- fresh
      
      res <- termAssertionGen env e1

      -- Update variable to fresh name bindings and generate assertions recursively
      let env' = M.insert r' beta (M.insert x alpha env)
      res' <- termAssertionGen env' e2

      -- Generate assertions
      let assertions = toAssertion env e1 (alpha :<:)
                    ++ toAssertion env e1 (beta :~:)

      return $ flatten [(assertions, []), res', res]

    Put e1 f e2 -> do
      alpha <- fresh
      beta  <- fresh

      res  <- termAssertionGen env e1
      res' <- termAssertionGen env e2

      let assertions = [alpha :<: beta] 
                    ++ toAssertion env e1 (beta :~:)
                    ++ toAssertion env e2 (alpha :~:)

      return $ flatten [(assertions, []), res', res]

    Member e f -> 
      termAssertionGen env e

    Case e1 _ x e2 y e3 -> do
      alpha <- fresh
      beta  <- fresh
      gamma <- fresh

      res <- termAssertionGen env e1

      let env' = M.insert x alpha env
      res' <- termAssertionGen env' e2

      let env'' = M.insert y gamma env
      res'' <- termAssertionGen env'' e3

      let assertions = toAssertion env e1 (beta :~:)
                    ++ [alpha :<: beta, gamma :~: beta]

      return $ flatten [(assertions, []), res, res', res'']

    Esac e1 _ x e2 -> do
      alpha <- fresh
      beta  <- fresh

      res <- termAssertionGen env e1

      let env' = M.insert x alpha env
      res' <- termAssertionGen env' e2

      let assertions = toAssertion env e1 (beta :~:)
                    ++ [alpha :<: beta]

      return $ flatten [(assertions, []), res, res']

    -- All other cases, like literals and nonrecursive expressions
    _ -> return ([],[])

  where
    
    toAssertion :: Env -> Expr -> (FreshVar -> Assertion) -> [Assertion]
    toAssertion env e f = 
      case getv env e of
        Just x -> [f x]
        Nothing -> []

    -- Returns the variable name from an environment if it exists, otherwise nothing
    getv :: Env -> Expr -> Maybe FreshVar 
    getv env e =
      case e of
        Var v -> Just $ env M.! v
        _ -> Nothing

    join :: [Fresh VarName ([a], [b])] -> Fresh VarName ([a], [b])
    join (e:es) = do
      (a,b) <- e
      (as,bs) <- join es
      return (a ++ as, b ++ bs)
    join [] = return ([],[])

    flatten :: [([a], [b])] -> ([a], [b])
    flatten (x:xs) = 
      let rest = flatten xs
      in (fst x ++ fst rest, snd x ++ snd rest)
    flatten [] = ([],[])

toGraph :: [Assertion] -> Graph
toGraph []     = mempty
toGraph (x:xs) = 
  case x of
    (a :<: b) -> addEdge b a $ toGraph xs
    (a :~: b) -> addEdge a b $ addEdge b a $ toGraph xs 
  where
    addEdge a b =
      M.insertWith (++) a [b]


hasPathTo :: Node -> Node -> Graph -> Bool
hasPathTo src dst g
  = hasPathTo' src dst g S.empty
    where
      hasPathTo' :: Node -> Node -> Graph -> S.Set Node -> Bool
      hasPathTo' s d g seen =
        case M.lookup s g of
          Nothing  -> False
          Just nbs ->
            any (\n -> 
                  n == dst ||
                    (notElem n seen &&
                      hasPathTo' n d g (S.insert n seen))
                ) nbs


-- To use:
--   run `dot -Tpdf graph.dot -o outfile.pdf`
-- where graph.dot is the output from this function.
genGraphDotFile :: String -> Graph -> [Node] -> [Node] -> String
genGraphDotFile name g args goals = 
  "digraph " ++ name ++ 
    " {\n"
      ++ "\tforcelabels=true;\n" 
      ++ highlight "blue" "argument" args
      ++ highlight "red"  "goal"     goals
      ++ intercalate "\n" (edges g) 
      ++ "\n}"
  where
    pairs :: Graph -> [(Node,Node)]
    pairs = concatMap (\(a, bs) -> map (\b -> (a,b)) bs) . M.assocs

    edges :: Graph -> [String]
    edges = map (\(a,b) -> "\t" ++ a ++ " -> " ++ b ++ ";") . pairs

    highlight :: String -> String -> [Node] -> String
    highlight color label nodes = "\t" ++ (concat . intersperse "\n" $
                                  map (\n -> n ++ " [ color = " ++ color ++ ", xlabel = " ++ label ++ " ];\n") nodes)
