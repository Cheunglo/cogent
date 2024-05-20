--
-- Copyright 2018, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{- LANGUAGE DeriveDataTypeable -}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{- LANGUAGE InstanceSigs -}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
#if __GLASGOW_HASKELL__ < 709
{-# LANGUAGE OverlappingInstances #-}
#endif
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-missing-signatures #-}

module Cogent.Core
  ( module Cogent.Core
  , module Cogent.Dargent.Core
  ) where

import Cogent.Common.Syntax hiding (Pragma)
import qualified Cogent.Common.Syntax as CS (Pragma)
import Cogent.Common.Types
import Cogent.Compiler
import Cogent.Dargent.Allocation (BitRange)
import Cogent.Dargent.Core
import Cogent.PrettyPrint hiding (associativity, primop)
import Cogent.Util
import Data.Fin
import Data.Nat (Nat(Zero, Suc), natToInt)
import qualified Data.Nat as Nat
import Data.Vec hiding (splitAt, length, zipWith, zip, unzip)
import qualified Data.Vec as Vec
import qualified Data.Map as M

import Control.Arrow hiding ((<+>))
import Data.Binary (Binary)
-- import Data.Data hiding (Refl)
import Data.Function ((&))
import Data.IntMap as IM (IntMap, null, filter, keys)
#if __GLASGOW_HASKELL__ < 709
import Data.Traversable(traverse)
#endif
import GHC.Generics (Generic)
--import Text.PrettyPrint.ANSI.Leijen as L hiding (tupled, indent, (<$>))
--import qualified Text.PrettyPrint.ANSI.Leijen as L ((<$>))
import Prettyprinter as L hiding (tupled, indent)
import Prettyprinter.Render.Terminal
import Isabelle.PrettyAnsi

type Pragma  b = CS.Pragma (SupposedlyMonoType b)
type Pragma_ b = CS.Pragma (Type 'Zero b)

data Type t b
  = TVar (Fin t)
  | TVarBang (Fin t)
  | TVarUnboxed (Fin t)
  | TCon TypeName [Type t b] (Sigil ()) -- Abstract type. Layout will be nothing.
  | TSyn TypeName [Type t b] (Sigil (DataLayout BitRange)) ReadOnly -- Preserved type synonym with optional layout
      -- the additional r/o specification is used for unboxed synonyms for a still linear type
      -- for boxed synonyms it is same as in sigil
  | TFun (Type t b) (Type t b)
  | TPrim PrimInt
  | TString
  | TSum [(TagName, (Type t b, Bool))]  -- True means taken (since 2.0.4)
  | TProduct (Type t b) (Type t b)
  | TRecord RecursiveParameter [(FieldName, (Type t b, Bool))] (Sigil (DataLayout BitRange))
    -- True means taken, Layout will be nothing for abstract types
  | TUnit
  | TRPar     RecParName (RecContext (Type t b))
  | TRParBang RecParName (RecContext (Type t b))
-- #ifdef BUILTIN_ARRAYS
  | TArray (Type t b) (LExpr t b) (Sigil (DataLayout BitRange)) (Maybe (LExpr t b))  -- the hole
  | TRefine (Type t b) (LExpr t b)
-- #endif
    -- The sigil specifies the layout of the element
  deriving (Show, Eq, Ord, Functor)

deriving instance Generic b => Generic (Type 'Zero b)

instance (Generic b, Binary b) => Binary (Type 'Zero b)


data SupposedlyMonoType b = forall (t :: Nat) (v :: Nat). SMT (Type t b)

instance Show b => Show (SupposedlyMonoType b) where
  show (SMT t) = show t


isTVar :: Type t b -> Bool
isTVar (TVar _) = True
isTVar _ = False

isTFun :: Type t b -> Bool
isTFun (TFun {}) = True
isTFun _ = False

isTRecord :: Type t b -> Bool
isTRecord (TRecord {}) = True
isTRecord _ = False

recordHasLayout :: Type t b -> Bool
recordHasLayout (TRecord _ _ (Boxed _ Layout{})) = True
recordHasLayout _ = False

-- ASSUME: input in a record type
recordFields :: Type t b -> [FieldName]
recordFields (TRecord _ fs _) = map fst fs
recordFields _ = __impossible "recordsFields: not a record type"

isUnboxed :: Type t b -> Bool
isUnboxed (TCon _ _ Unboxed) = True
isUnboxed (TSyn _ _ Unboxed _) = True
isUnboxed (TRecord _ _ Unboxed) =  True
#ifdef BUILTIN_ARRAYS
isUnboxed (TArray _ _ Unboxed _) = True
#endif
#ifdef REFINEMENT_TYPES
isUnboxed (TRefine t _) = isUnboxed t
#endif
isUnboxed _ = False

unroll :: RecParName -> RecContext (Type t b) -> Type t b
unroll v (Just ctxt) = erp (Just ctxt) (ctxt M.! v)
  where
    -- Embed rec pars
    erp :: RecContext (Type t b) -> Type t b -> Type t b
    erp c (TCon n ts s) = TCon n (map (erp c) ts) s
    erp c (TSyn _ _ _ _) = __impossible "unroll applied to type synonym. Please unfold type synonyms before applying unroll."
    erp c (TFun t1 t2) = TFun (erp c t1) (erp c t2)
    erp c (TSum r) = TSum $ map (\(a,(t,b)) -> (a, (erp c t, b))) r
    erp c (TProduct t1 t2) = TProduct (erp c t1) (erp c t2)
    erp (Just c) t@(TRecord rp fs s) =
      let c' = case rp of Rec v -> M.insert v t c; _ -> c
      in TRecord rp (map (\(a,(t,b)) -> (a, (erp (Just c') t, b))) fs) s
    -- Context must be Nothing at this point
    erp c (TRPar v Nothing) = TRPar v c
#ifdef BUILTIN_ARRAYS
    erp c (TArray t e s h) = TArray (erp c t) e s h
#endif
    erp _ t = t
unroll v _ = __impossible "unroll in core given an empty context - this usually means a recursive parameter was not unrolled before being used"

data FunNote = NoInline | InlineMe | MacroCall | InlinePlease  -- order is important, larger value has stronger precedence
             deriving (Bounded, Eq, Ord, Show)

data Expr t v a b e
  = Variable (Fin v, a)
  | Fun CoreFunName [Type t b] [DataLayout BitRange] FunNote  -- here do we want to keep partial application and infer again? / zilinc
  | Op Op [e t v a b]
  | App (e t v a b) (e t v a b)
  | Con TagName (e t v a b) (Type t b)
  | Unit
  | ILit Integer PrimInt
  | SLit String
#ifdef BUILTIN_ARRAYS
  | ALit [e t v a b]
  | ArrayIndex (e t v a b) (e t v a b)
  | Pop (a, a) (e t v a b) (e t ('Suc ('Suc v)) a b)
  | Singleton (e t v a b)  -- extracting the element out of a singleton array
  | ArrayMap2 ((a, a), e t ('Suc ('Suc v)) a b) (e t v a b, e t v a b)
  | ArrayTake (a, a) (e t v a b) (e t v a b) (e t ('Suc ('Suc v)) a b)
          -- \ ^^^ The first is the taken object, and the second is the array
  | ArrayPut (e t v a b) (e t v a b) (e t v a b)
#endif
  | Let a (e t v a b) (e t ('Suc v) a b)
  | LetBang [(Fin v, a)] a (e t v a b) (e t ('Suc v) a b)
  | Tuple (e t v a b) (e t v a b)
  | Struct [(FieldName, e t v a b)]  -- unboxed record
  | If (e t v a b) (e t v a b) (e t v a b)   -- technically no longer needed as () + () == Bool
  | Case (e t v a b) TagName (Likelihood, a, e t ('Suc v) a b) (Likelihood, a, e t ('Suc v) a b)
  | Esac (e t v a b)
  | Split (a, a) (e t v a b) (e t ('Suc ('Suc v)) a b)
  | Member (e t v a b) FieldIndex
  | Take (a, a) (e t v a b) FieldIndex (e t ('Suc ('Suc v)) a b)
     -- \ ^^^ The first is the taken field, and the second is the record
  | Put (e t v a b) FieldIndex (e t v a b)
  | Promote (Type t b) (e t v a b)  -- only for guiding the tc. rep. unchanged.
  | Cast (Type t b) (e t v a b)  -- only for integer casts. rep. changed
-- \ vvv constraint no smaller than header, thus UndecidableInstances
deriving instance (Show a, Show b, Show (e t v a b), Show (e t ('Suc v) a b), Show (e t ('Suc ('Suc v)) a b))
  => Show (Expr t v a b e)
deriving instance (Eq a, Eq b, Eq (e t v a b), Eq (e t ('Suc v) a b), Eq (e t ('Suc ('Suc v)) a b))
  => Eq  (Expr t v a b e)
deriving instance (Ord a, Ord b, Ord (e t v a b), Ord (e t ('Suc v) a b), Ord (e t ('Suc ('Suc v)) a b))
  => Ord (Expr t v a b e)

-- NOTE: We leave these logic expressions here even when the --builtin-arrays
-- flag is off. The reason is that, without it, the type class instance
-- derivings don't work. It's very mysterious to me. / zilinc
data LExpr t b
  = LVariable (Nat, b)
  | LFun CoreFunName [Type t b] [DataLayout BitRange]
  | LOp Op [LExpr t b]
  | LApp (LExpr t b) (LExpr t b)
  | LCon TagName (LExpr t b) (Type t b)
  | LUnit
  | LILit Integer PrimInt
  | LSLit String
  | LLet b (LExpr t b) (LExpr t b)
  | LLetBang [(Nat, b)] b (LExpr t b) (LExpr t b)
  | LTuple (LExpr t b) (LExpr t b)
  | LStruct [(FieldName, LExpr t b)]  -- unboxed record
  | LIf (LExpr t b) (LExpr t b) (LExpr t b)   -- technically no longer needed as () + () == Bool
  | LCase (LExpr t b) TagName (b, LExpr t b) (b, LExpr t b)
  | LEsac (LExpr t b)
  | LSplit (b, b) (LExpr t b) (LExpr t b)
  | LMember (LExpr t b) FieldIndex
  | LTake (b, b) (LExpr t b) FieldIndex (LExpr t b)
     -- \ ^^^ The first is the record, and the second is the taken field
  | LPut (LExpr t b) FieldIndex (LExpr t b)
  | LPromote (Type t b) (LExpr t b)  -- only for guiding the tc. rep. unchanged.
  | LCast (Type t b) (LExpr t b)  
  deriving (Show, Eq, Ord, Functor, Generic)

instance (Binary b, Generic b) => Binary (LExpr 'Zero b)

#ifdef BUILTIN_ARRAYS
exprToLExpr :: (a -> b)
            -> ((a -> b) -> e t v a b -> LExpr t b)
            -> ((a -> b) -> e t ('Suc v) a b -> LExpr t b)
            -> ((a -> b) -> e t ('Suc ('Suc v)) a b -> LExpr t b)
            -> Expr t v a b e -> LExpr t b
exprToLExpr fab f f1 f2 = \case
  Variable v         -> LVariable (second fab $ first finNat v)
  Fun fn ts ls nt    -> LFun fn ts ls
  Op opr es          -> LOp opr (map f' es)
  App e1 e2          -> LApp (f' e1) (f' e2)
  Con cn e t         -> LCon cn (f' e) t
  Unit               -> LUnit
  ILit i pt          -> LILit i pt
  SLit s             -> LSLit s
  ALit {}            -> __impossible "array expressions in types not allowed" 
  ArrayIndex {}      -> __impossible "array expressions in types not allowed"
  ArrayMap2 {}       -> __impossible "array expressions in types not allowed"
  Pop {}             -> __impossible "array expressions in types not allowed"
  Singleton {}       -> __impossible "array expressions in types not allowed"
  ArrayTake {}       -> __impossible "array expressions in types not allowed"
  ArrayPut {}        -> __impossible "array expressions in types not allowed"
  Let a e1 e2        -> LLet (fab a) (f' e1) (f1' e2)
  LetBang vs a e1 e2 -> LLetBang (map (second fab . first finNat) vs) (fab a) (f' e1) (f1' e2)
  Tuple e1 e2        -> LTuple (f' e1) (f' e2)
  Struct fs          -> LStruct (map (second f') fs)
  If e1 e2 e3        -> LIf (f' e1) (f' e2) (f' e3)
  Case e tn (l1,a1,e1) (l2,a2,e2) -> LCase (f' e) tn (fab a1, f1' e1) (fab a2, f1' e2)
  Esac e             -> LEsac (f' e)
  Split a e1 e2      -> LSplit (both fab a) (f' e1) (f2' e2)
  Member rec fld     -> LMember (f' rec) fld
  Take a rec fld e   -> LTake (both fab a) (f' rec) fld (f2' e)
  Put rec fld v      -> LPut (f' rec) fld (f' v)
  Promote ty e       -> LPromote ty (f' e)
  Cast ty e          -> LCast ty (f' e)
 where
  f'  = f  fab
  f1' = f1 fab
  f2' = f2 fab

texprToLExpr :: (a -> b) -> TypedExpr t v a b -> LExpr t b
texprToLExpr f (TE _ e) = exprToLExpr f texprToLExpr texprToLExpr texprToLExpr e

uexprToLExpr :: (a -> b) -> UntypedExpr t v a b -> LExpr t b
uexprToLExpr f (E e) = exprToLExpr f uexprToLExpr uexprToLExpr uexprToLExpr e
#endif

data UntypedExpr t v a b = E  (Expr t v a b UntypedExpr) deriving (Show, Eq, Ord)
data TypedExpr   t v a b = TE { exprType :: Type t b , exprExpr :: Expr t v a b TypedExpr }
                         deriving (Show, Eq, Ord)

data FunctionType b = forall t l. FT (Vec t Kind) (Vec l (Type t b)) (Type t b) (Type t b)
deriving instance Show a => Show (FunctionType a)

data Attr = Attr { inlineDef :: Bool, fnMacro :: Bool } deriving (Eq, Ord, Show, Generic)

instance Binary Attr

#if __GLASGOW_HASKELL__ < 803
instance Monoid Attr where
  mempty = Attr False False
  (Attr a1 a2) `mappend` (Attr a1' a2') = Attr (a1 || a1') (a2 || a2')
#else
instance Semigroup Attr where
  Attr a1 a2 <> Attr a1' a2' = Attr (a1 || a1') (a2 || a2')
instance Monoid Attr where
  mempty = Attr False False
#endif


data Definition e a b
  = forall t l. (PrettyAnsi a, PrettyAnsi b, PrettyAnsi (e t ('Suc 'Zero) a b))
             => FunDef  Attr FunName (Vec t (TyVarName, Kind)) (Vec l (DLVarName, Type t b)) (Type t b) (Type t b) (e t ('Suc 'Zero) a b)
  | forall t l. AbsDecl Attr FunName (Vec t (TyVarName, Kind)) (Vec l (DLVarName, Type t b)) (Type t b) (Type t b)
  | forall t. TypeDef TypeName (Vec t TyVarName) (Maybe (Type t b))
deriving instance (Show a, Show b) => Show (Definition TypedExpr   a b)
deriving instance (Show a, Show b) => Show (Definition UntypedExpr a b)

type CoreConst e = (VarName, e 'Zero 'Zero VarName VarName)

getDefinitionId :: Definition e a b -> String
getDefinitionId (FunDef  _ fn _ _ _ _ _) = fn
getDefinitionId (AbsDecl _ fn _ _ _ _  ) = fn
getDefinitionId (TypeDef tn _ _    ) = tn

getFuncId :: Definition e a b -> Maybe FunName
getFuncId (FunDef  _ fn _ _ _ _ _) = Just fn
getFuncId (AbsDecl _ fn _ _ _ _  ) = Just fn
getFuncId _ = Nothing

getTypeVarNum :: Definition e a b -> Int
getTypeVarNum (FunDef  _ _ tvs _ _ _ _) = Nat.toInt $ Vec.length tvs
getTypeVarNum (AbsDecl _ _ tvs _ _ _  ) = Nat.toInt $ Vec.length tvs
getTypeVarNum (TypeDef _ tvs _        ) = Nat.toInt $ Vec.length tvs

getLayoutVarNum :: Definition e a b -> Int
getLayoutVarNum (FunDef  _ _ _ lvs _ _ _) = Nat.toInt $ Vec.length lvs
getLayoutVarNum (AbsDecl _ _ _ lvs _ _  ) = Nat.toInt $ Vec.length lvs
getLayoutVarNum (TypeDef _ _ _          ) = 0

isDefinitionId :: String -> Definition e a b -> Bool
isDefinitionId n d = n == getDefinitionId d

isFuncId :: CoreFunName -> Definition e a b -> Bool
isFuncId n (FunDef  _ fn _ _ _ _ _) = unCoreFunName n == fn
isFuncId n (AbsDecl _ fn _ _ _ _  ) = unCoreFunName n == fn
isFuncId _ _ = False

isAbsFun :: Definition e a b -> Bool
isAbsFun (AbsDecl {}) = True
isAbsFun _ = False

isConFun :: Definition e a b -> Bool
isConFun (FunDef {}) = True
isConFun _ = False

isTypeDef :: Definition e a b -> Bool
isTypeDef (TypeDef {}) = True
isTypeDef _ = False

isAbsTyp :: Definition e a b -> Bool
isAbsTyp (TypeDef _ _ Nothing) = True
isAbsTyp _ = False

findFuncById :: CoreFunName -> [Definition e a b] -> Maybe (Definition e a b)
findFuncById fn [] = Nothing
findFuncById fn (d:ds) | isFuncId fn d = Just d
                       | otherwise = findFuncById fn ds

insertIdxAtType :: Nat -> Type t b -> Type t b
insertIdxAtType cut t = __fixme t

insertIdxAtUntypedExpr :: Fin ('Suc v) -> UntypedExpr t v a b -> UntypedExpr t ('Suc v) a b
insertIdxAtUntypedExpr cut (E e) = E $ insertIdxAtE cut insertIdxAtUntypedExpr e

insertIdxAtTypedExpr :: Fin ('Suc v) -> TypedExpr t v a b -> TypedExpr t ('Suc v) a b
insertIdxAtTypedExpr cut (TE t e) = TE (insertIdxAtType (finNat cut) t) (insertIdxAtE cut insertIdxAtTypedExpr e)

insertIdxAtE :: Fin ('Suc v)
             -> (forall v. Fin ('Suc v) -> e t v a b -> e t ('Suc v) a b)
             -> (Expr t v a b e -> Expr t ('Suc v) a b e)
insertIdxAtE cut f (Variable v) = Variable $ first (liftIdx cut) v
insertIdxAtE cut f (Fun fn ts ls nt) = Fun fn ts ls nt
insertIdxAtE cut f (Op opr es) = Op opr $ map (f cut) es
insertIdxAtE cut f (App e1 e2) = App (f cut e1) (f cut e2)
insertIdxAtE cut f (Con tag e t) = Con tag (f cut e) t
insertIdxAtE cut f (Unit) = Unit
insertIdxAtE cut f (ILit n pt) = ILit n pt
insertIdxAtE cut f (SLit s) = SLit s
#ifdef BUILTIN_ARRAYS
insertIdxAtE cut f (ALit es) = ALit $ map (f cut) es
insertIdxAtE cut f (ArrayIndex e l) = ArrayIndex (f cut e) (f cut l)
insertIdxAtE cut f (Pop a e1 e2) = Pop a (f cut e1) (f (FSuc (FSuc cut)) e2)
insertIdxAtE cut f (Singleton e) = Singleton (f cut e)
insertIdxAtE cut f (ArrayPut arr i e) = ArrayPut (f cut arr) (f cut i) (f cut e)
insertIdxAtE cut f (ArrayTake (o, ca) pa i e) = ArrayTake (o, ca) (f cut pa) (f cut i) (f (FSuc (FSuc cut)) e)
#endif
insertIdxAtE cut f (Let a e1 e2) = Let a (f cut e1) (f (FSuc cut) e2)
insertIdxAtE cut f (LetBang vs a e1 e2) = LetBang (map (first $ liftIdx cut) vs) a (f cut e1) (f (FSuc cut) e2)
insertIdxAtE cut f (Tuple e1 e2) = Tuple (f cut e1) (f cut e2)
insertIdxAtE cut f (Struct fs) = Struct $ map (second $ f cut) fs
insertIdxAtE cut f (If c e1 e2) = If (f cut c) (f cut e1) (f cut e2)
insertIdxAtE cut f (Case c tag (l1,a1,alt) (l2,a2,alts)) = Case (f cut c) tag (l1, a1, f (FSuc cut) alt) (l2, a2, f (FSuc cut) alts)
insertIdxAtE cut f (Esac e) = Esac (f cut e)
insertIdxAtE cut f (Split a e1 e2) = Split a (f cut e1) (f (FSuc (FSuc cut)) e2)
insertIdxAtE cut f (Member e fld) = Member (f cut e) fld
insertIdxAtE cut f (Take a rec fld e) = Take a (f cut rec) fld (f (FSuc (FSuc cut)) e)
insertIdxAtE cut f (Put rec fld e) = Put (f cut rec) fld (f cut e)
insertIdxAtE cut f (Promote ty e) = Promote ty (f cut e)
insertIdxAtE cut f (Cast ty e) = Cast ty (f cut e)



-- pre-order fold over Expr wrapper
foldEPre :: (Monoid m)
         => (forall t v. e1 t v a b -> Expr t v a b e1)
         -> (forall t v. e1 t v a b -> m)
         -> e1 t v a b
         -> m
foldEPre unwrap f e = case unwrap e of
  Variable{}          -> f e
  Fun{}               -> f e
  (Op _ es)           -> mconcat $ f e : map (foldEPre unwrap f) es
  (App e1 e2)         -> mconcat [f e, foldEPre unwrap f e1, foldEPre unwrap f e2]
  (Con _ e1 _)        -> f e `mappend` foldEPre unwrap f e1
  Unit                -> f e
  ILit {}             -> f e
  SLit {}             -> f e
#ifdef BUILTIN_ARRAYS
  ALit es             -> mconcat $ f e : map (foldEPre unwrap f) es
  ArrayIndex e i      -> mconcat [f e, f i]
  Pop as e1 e2        -> mconcat [f e1, f e2]
  Singleton e         -> f e
  ArrayMap2 (_,e) (e1,e2) -> mconcat [f e, f e1, f e2]
  ArrayTake _ arr fld e   -> mconcat [f arr, f fld, f e]
  ArrayPut    arr fld e   -> mconcat [f arr, f fld, f e]
#endif
  (Let _ e1 e2)       -> mconcat [f e, foldEPre unwrap f e1, foldEPre unwrap f e2]
  (LetBang _ _ e1 e2) -> mconcat [f e, foldEPre unwrap f e1, foldEPre unwrap f e2]
  (Tuple e1 e2)       -> mconcat [f e, foldEPre unwrap f e1, foldEPre unwrap f e2]
  (Struct fs)         -> mconcat $ f e : map (foldEPre unwrap f . snd) fs
  (If e1 e2 e3)       -> mconcat [f e, foldEPre unwrap f e1, foldEPre unwrap f e2, foldEPre unwrap f e3]
  (Case e1 _ (_,_,e2) (_,_,e3)) -> mconcat $ [f e, foldEPre unwrap f e1, foldEPre unwrap f e2, foldEPre unwrap f e3]
  (Esac e1)           -> f e `mappend` foldEPre unwrap f e1
  (Split _ e1 e2)     -> mconcat [f e, foldEPre unwrap f e1, foldEPre unwrap f e2]
  (Member e1 _)       -> f e `mappend` foldEPre unwrap f e1
  (Take _ e1 _ e2)    -> mconcat [f e, foldEPre unwrap f e1, foldEPre unwrap f e2]
  (Put e1 _ e2)       -> mconcat [f e, foldEPre unwrap f e1, foldEPre unwrap f e2]
  (Promote _ e1)      -> f e `mappend` foldEPre unwrap f e1
  (Cast _ e1)         -> f e `mappend` foldEPre unwrap f e1


fmapE :: (forall t v. e1 t v a b -> e2 t v a b) -> Expr t v a b e1 -> Expr t v a b e2
fmapE f (Variable v)         = Variable v
fmapE f (Fun fn ts ls nt)    = Fun fn ts ls nt
fmapE f (Op opr es)          = Op opr (map f es)
fmapE f (App e1 e2)          = App (f e1) (f e2)
fmapE f (Con cn e t)         = Con cn (f e) t
fmapE f (Unit)               = Unit
fmapE f (ILit i pt)          = ILit i pt
fmapE f (SLit s)             = SLit s
#ifdef BUILTIN_ARRAYS
fmapE f (ALit es)            = ALit (map f es)
fmapE f (ArrayIndex e i)     = ArrayIndex (f e) (f i)
fmapE f (ArrayMap2 (as,e) (e1,e2)) = ArrayMap2 (as, f e) (f e1, f e2)
fmapE f (Pop a e1 e2)        = Pop a (f e1) (f e2)
fmapE f (Singleton e)        = Singleton (f e)
fmapE f (ArrayTake as arr fld e) = ArrayTake as (f arr) (f fld) (f e)
fmapE f (ArrayPut arr fld e) = ArrayPut (f arr) (f fld) (f e)
#endif
fmapE f (Let a e1 e2)        = Let a (f e1) (f e2)
fmapE f (LetBang vs a e1 e2) = LetBang vs a (f e1) (f e2)
fmapE f (Tuple e1 e2)        = Tuple (f e1) (f e2)
fmapE f (Struct fs)          = Struct (map (second f) fs)
fmapE f (If e1 e2 e3)        = If (f e1) (f e2) (f e3)
fmapE f (Case e tn (l1,a1,e1) (l2,a2,e2)) = Case (f e) tn (l1, a1, f e1) (l2, a2, f e2)
fmapE f (Esac e)             = Esac (f e)
fmapE f (Split a e1 e2)      = Split a (f e1) (f e2)
fmapE f (Member rec fld)     = Member (f rec) fld
fmapE f (Take a rec fld e)   = Take a (f rec) fld (f e)
fmapE f (Put rec fld v)      = Put (f rec) fld (f v)
fmapE f (Promote ty e)       = Promote ty (f e)
fmapE f (Cast ty e)          = Cast ty (f e)


untypeE :: TypedExpr t v a b -> UntypedExpr t v a b
untypeE (TE _ e) = E $ fmapE untypeE e

untypeD :: Definition TypedExpr a b -> Definition UntypedExpr a b
untypeD (FunDef  attr fn ts ls ti to e) = FunDef  attr fn ts ls ti to (untypeE e)
untypeD (AbsDecl attr fn ts ls ti to  ) = AbsDecl attr fn ts ls ti to
untypeD (TypeDef tn ts mt) = TypeDef tn ts mt

instance (Functor (e t v a),
          Functor (e t ('Suc v) a),
          Functor (e t ('Suc ('Suc v)) a))
       => Functor (Flip (Expr t v a) e) where  -- map over @b@
  fmap f (Flip (Variable v)         )      = Flip $ Variable v
  fmap f (Flip (Fun fn ts ls nt)    )      = Flip $ Fun fn (fmap (fmap f) ts) ls nt
  fmap f (Flip (Op opr es)          )      = Flip $ Op opr (fmap (fmap f) es)
  fmap f (Flip (App e1 e2)          )      = Flip $ App (fmap f e1) (fmap f e2)
  fmap f (Flip (Con cn e t)         )      = Flip $ Con cn (fmap f e) (fmap f t)
  fmap f (Flip (Unit)               )      = Flip $ Unit
  fmap f (Flip (ILit i pt)          )      = Flip $ ILit i pt
  fmap f (Flip (SLit s)             )      = Flip $ SLit s
#ifdef BUILTIN_ARRAYS
  fmap f (Flip (ALit es)            )      = Flip $ ALit (fmap (fmap f) es)
  fmap f (Flip (ArrayIndex e i)     )      = Flip $ ArrayIndex (fmap f e) (fmap f i)
  fmap f (Flip (ArrayMap2 (as,e) (e1,e2))) = Flip $ ArrayMap2 (as, fmap f e) (fmap f e1, fmap f e2)
  fmap f (Flip (Pop as e1 e2)       )      = Flip $ Pop as (fmap f e1) (fmap f e2)
  fmap f (Flip (Singleton e)        )      = Flip $ Singleton (fmap f e)
  fmap f (Flip (ArrayTake as arr fld e))   = Flip $ ArrayTake as (fmap f arr) (fmap f fld) (fmap f e)
  fmap f (Flip (ArrayPut     arr fld e))   = Flip $ ArrayPut (fmap f arr) (fmap f fld) (fmap f e)
#endif
  fmap f (Flip (Let a e1 e2)        )      = Flip $ Let a (fmap f e1) (fmap f e2)
  fmap f (Flip (LetBang vs a e1 e2) )      = Flip $ LetBang vs a (fmap f e1) (fmap f e2)
  fmap f (Flip (Tuple e1 e2)        )      = Flip $ Tuple (fmap f e1) (fmap f e2)
  fmap f (Flip (Struct fs)          )      = Flip $ Struct (map (second $ fmap f) fs)
  fmap f (Flip (If e1 e2 e3)        )      = Flip $ If (fmap f e1) (fmap f e2) (fmap f e3)
  fmap f (Flip (Case e tn (l1,a1,e1) (l2,a2,e2))) = Flip $ Case (fmap f e) tn (l1, a1, fmap f e1) (l2, a2, fmap f e2)
  fmap f (Flip (Esac e)             )      = Flip $ Esac (fmap f e)
  fmap f (Flip (Split a e1 e2)      )      = Flip $ Split a (fmap f e1) (fmap f e2)
  fmap f (Flip (Member rec fld)     )      = Flip $ Member (fmap f rec) fld
  fmap f (Flip (Take a rec fld e)   )      = Flip $ Take a (fmap f rec) fld (fmap f e)
  fmap f (Flip (Put rec fld v)      )      = Flip $ Put (fmap f rec) fld (fmap f v)
  fmap f (Flip (Promote ty e)       )      = Flip $ Promote (fmap f ty) (fmap f e)
  fmap f (Flip (Cast ty e)          )      = Flip $ Cast (fmap f ty) (fmap f e)

instance (Functor (Flip (e t v) b),
          Functor (Flip (e t ('Suc v)) b),
          Functor (Flip (e t ('Suc ('Suc v))) b))
       => Functor (Flip2 (Expr t v) e b) where  -- map over @a@
  fmap f (Flip2 (Variable v)         )      = Flip2 $ Variable (second f v)
  fmap f (Flip2 (Fun fn ts ls nt)    )      = Flip2 $ Fun fn ts ls nt
  fmap f (Flip2 (Op opr es)          )      = Flip2 $ Op opr (fmap (ffmap f) es)
  fmap f (Flip2 (App e1 e2)          )      = Flip2 $ App (ffmap f e1) (ffmap f e2)
  fmap f (Flip2 (Con cn e t)         )      = Flip2 $ Con cn (ffmap f e) t
  fmap f (Flip2 (Unit)               )      = Flip2 $ Unit
  fmap f (Flip2 (ILit i pt)          )      = Flip2 $ ILit i pt
  fmap f (Flip2 (SLit s)             )      = Flip2 $ SLit s
#ifdef BUILTIN_ARRAYS
  fmap f (Flip2 (ALit es)            )      = Flip2 $ ALit (fmap (ffmap f) es)
  fmap f (Flip2 (ArrayIndex e i)     )      = Flip2 $ ArrayIndex (ffmap f e) (ffmap f i)
  fmap f (Flip2 (ArrayMap2 (as,e) (e1,e2))) = Flip2 $ ArrayMap2 (both f as, ffmap f e) (ffmap f e1, ffmap f e2)
  fmap f (Flip2 (Pop as e1 e2)       )      = Flip2 $ Pop (both f as) (ffmap f e1) (ffmap f e2)
  fmap f (Flip2 (Singleton e)        )      = Flip2 $ Singleton (ffmap f e)
  fmap f (Flip2 (ArrayTake as arr fld e))   = Flip2 $ ArrayTake (both f as) (ffmap f arr) (ffmap f fld) (ffmap f e)
  fmap f (Flip2 (ArrayPut     arr fld e))   = Flip2 $ ArrayPut (ffmap f arr) (ffmap f fld) (ffmap f e)
#endif
  fmap f (Flip2 (Let a e1 e2)        )      = Flip2 $ Let (f a) (ffmap f e1) (ffmap f e2)
  fmap f (Flip2 (LetBang vs a e1 e2) )      = Flip2 $ LetBang (map (second f) vs) (f a) (ffmap f e1) (ffmap f e2)
  fmap f (Flip2 (Tuple e1 e2)        )      = Flip2 $ Tuple (ffmap f e1) (ffmap f e2)
  fmap f (Flip2 (Struct fs)          )      = Flip2 $ Struct (map (second $ ffmap f) fs)
  fmap f (Flip2 (If e1 e2 e3)        )      = Flip2 $ If (ffmap f e1) (ffmap f e2) (ffmap f e3)
  fmap f (Flip2 (Case e tn (l1,a1,e1) (l2,a2,e2))) = Flip2 $ Case (ffmap f e) tn (l1, f a1, ffmap f e1) (l2, f a2, ffmap f e2)
  fmap f (Flip2 (Esac e)             )      = Flip2 $ Esac (ffmap f e)
  fmap f (Flip2 (Split a e1 e2)      )      = Flip2 $ Split (both f a) (ffmap f e1) (ffmap f e2)
  fmap f (Flip2 (Member rec fld)     )      = Flip2 $ Member (ffmap f rec) fld
  fmap f (Flip2 (Take a rec fld e)   )      = Flip2 $ Take (both f a) (ffmap f rec) fld (ffmap f e)
  fmap f (Flip2 (Put rec fld v)      )      = Flip2 $ Put (ffmap f rec) fld (ffmap f v)
  fmap f (Flip2 (Promote ty e)       )      = Flip2 $ Promote ty (ffmap f e)
  fmap f (Flip2 (Cast ty e)          )      = Flip2 $ Cast ty (ffmap f e)

instance Functor (Flip (TypedExpr t v) b) where  -- over @a@
  fmap f (Flip (TE t e)) = Flip $ TE t (fffmap f e)


-- instance Functor (Definition TypedExpr) where
--   fmap f (FunDef  attr fn ts ti to e) = FunDef  attr fn ts ti to (fmap f e)
--   fmap f (AbsDecl attr fn ts ti to)   = AbsDecl attr fn ts ti to
--   fmap f (TypeDef tn ts mt)      = TypeDef tn ts mt
--
-- stripNameTD :: Definition TypedExpr VarName -> Definition TypedExpr ()
-- stripNameTD = fmap $ const ()


-- /////////////////////////////////////////////////////////////////////////////
-- Core-lang -printing

primop = blue . (ansiP :: Op -> Doc AnsiStyle)
fieldIndex = magenta . string . ('.':) . show

-- NOTE: the precedence levels are somewhat different to those of the surface lang / zilinc

instance Prec (Expr t v a b e) where
  prec (Op opr [_,_]) = prec (associativity opr)
  prec (ILit {}) = 0
  prec (SLit {}) = 0
#ifdef BUILTIN_ARRAYS
  prec (ALit {}) = 0
#endif
  prec (Variable {}) = 0
  prec (Fun {}) = 0
  prec (App {}) = 1
  prec (Tuple {}) = 0
  prec (Con {}) = 0
  prec (Esac {}) = 0
  prec (Member {}) = 0
  prec (Take {}) = 0
  prec (Put {}) = 1
  prec (Promote {}) = 0
  prec (Cast {}) = 0
  prec _ = 100

instance Prec (TypedExpr t v a b) where
  prec (TE _ e) = prec e

instance Prec (UntypedExpr t v a b) where
  prec (E e) = prec e

#ifdef BUILTIN_ARRAYS
instance Prec (LExpr t b) where
  prec (LOp opr [_,_]) = prec (associativity opr)
  prec (LILit {}) = 0
  prec (LSLit {}) = 0
  prec (LVariable {}) = 0
  prec (LFun {}) = 0
  prec (LApp {}) = 1
  prec (LTuple {}) = 0
  prec (LCon {}) = 0
  prec (LEsac {}) = 0
  prec (LMember {}) = 0
  prec (LTake {}) = 0
  prec (LPut {}) = 1
  prec (LPromote {}) = 0
  prec (LCast {}) = 0
  prec _ = 100
#endif

vF = dullblue  . string . ("_v" ++) . show . finInt
tF = dullgreen . string . ("_t" ++) . show . finInt

instance (PrettyAnsi a, PrettyAnsi b) => PrettyAnsi (TypedExpr t v a b) where
  ansiP (TE t e) | not __cogent_fshow_types_in_ = ansiP e
                  | otherwise = parens (ansiP e <+> symbol ":" <+> ansiP t)

instance (PrettyAnsi a, PrettyAnsi b) => PrettyAnsi (UntypedExpr t v a b) where
  ansiP (E e) = ansiP e

instance (PrettyAnsi a, PrettyAnsi b, Prec (e t v a b), PrettyAnsi (e t v a b), PrettyAnsi (e t ('Suc v) a b), PrettyAnsi (e t ('Suc ('Suc v)) a b))
         => PrettyAnsi (Expr t v a b e) where
  ansiP (Op opr [a,b])
     | LeftAssoc  l <- associativity opr = Prec (l+1) a <+> primop opr <+> prettyPrec l b
     | RightAssoc l <- associativity opr = Prec l a <+> primop opr <+> prettyPrec (l+1)  b
     | NoAssoc    l <- associativity opr = Prec l a <+> primop opr <+> prettyPrec l  b
  ansiP (Op opr [e]) = primop opr <+> Prec 1 e
  ansiP (Op opr es)  = primop opr <+> tupled (map ansiP es)
  ansiP (ILit i pt) = literal (string $ show i) <+> symbol "::" <+> ansiP pt
  ansiP (SLit s) = literal $ string s
#ifdef BUILTIN_ARRAYS
  ansiP (ALit es) = array $ map ansiP es
  ansiP (ArrayIndex arr idx) = Prec 2 arr <+> symbol "@" <+> prettyPrec 2 idx
  ansiP (ArrayMap2 ((v1,v2),f) (e1,e2)) = keyword "map2" <+>
                                           parens (symbol "\\" <> ansiP v1 <+> ansiP v2 <+> symbol "=>" <+> ansiP f) <+>
                                           Prec 1 e1 <+> prettyPrec 1 e2
  ansiP (Pop (v1,v2) e1 e2) = align (keyword "pop" <+> ansiP v1 <> symbol ":@" <> ansiP v2 <+> symbol "=" <+> ansiP e1 `vsep2`
                                keyword "in"  <+> ansiP e2)
  ansiP (Singleton e) = keyword "singleton" <+> parens (ansiP e)
  ansiP (ArrayPut arr i e) = Prec 1 arr <+> symbol "@" <> record [symbol "@" <> ansiP i <+> symbol "=" <+> ansiP e]
  ansiP (ArrayTake (o, ca) pa i e) = align (keyword "take" <+> ansiP ca <+> symbol "@" <> record [symbol "@" <> ansiP i <+>
                                             symbol "=" <+> ansiP o] <+> symbol "=" <+> (Prec 1 pa) `vsep2` keyword "in" <+> ansiP e)
#endif
  ansiP (Variable x) = ansiP (snd x) L.<> angles (vF $ fst x)
  ansiP (Fun fn ts ls nt) = ansiP nt L.<> funname (unCoreFunName fn) <+> ansiP ts <+> ansiP ls
  ansiP (App a b) = Prec 2 a <+> prettyPrec 1 b
  ansiP (Let a e1 e2) = align (keyword "let" <+> ansiP a <+> symbol "=" <+> ansiP e1 `vsep2`
                                keyword "in" <+> ansiP e2)
  ansiP (LetBang bs a e1 e2) = align (keyword "let!" <+> tupled (map (vF . fst) bs) <+> ansiP a <+> symbol "=" <+> ansiP e1 `vsep2`
                                       keyword "in" <+> ansiP e2)
  ansiP (Unit) = tupled []
  ansiP (Tuple e1 e2) = tupled (map ansiP [e1, e2])
  ansiP (Struct fs) = symbol "#" L.<> record (map (\(n,e) -> fieldname n <+> symbol "=" <+> ansiP e) fs)
  ansiP (Con tn e t) = parens (tagname tn <+> Prec 1 e) <+> symbol "::" <+> ansiP t
  ansiP (If c t e) = group . align $ (keyword "if" <+> ansiP c
                                       `vsep2` indent (keyword "then" </> align (ansiP t))
                                       `vsep2` indent (keyword "else" </> align (ansiP e)))
  ansiP (Case e tn (l1,v1,a1) (l2,v2,a2)) = align (keyword "case" <+> ansiP e <+> keyword "of"
                                                  `vsep2` indent (tagname tn <+> ansiP v1 <+> ansiP l1 <+> align (ansiP a1))
                                                  `vsep2` indent (ansiP v2 <+> ansiP l2 <+> align (ansiP a2)))
  ansiP (Esac e) = keyword "esac" <+> parens (ansiP e)
  ansiP (Split (v1,v2) e1 e2) = align (keyword "split" <+> parens (ansiP v1 <> comma <> ansiP v2) <+> symbol "=" <+> ansiP e1 `vsep2`
                                  keyword "in" <+> ansiP e2)
  ansiP (Member x f) = Prec 1 x L.<> symbol "." L.<> fieldIndex f
  ansiP (Take (a,b) rec f e) = align (keyword "take" <+> tupled [ansiP a, ansiP b] <+> symbol "="
                                                      <+> Prec 1 rec <+> record (fieldIndex f:[]) `vsep2`
                                       keyword "in" <+> ansiP e)
  ansiP (Put rec f v) = Prec 1 rec <+> record [fieldIndex f <+> symbol "=" <+> ansiP v]
  ansiP (Promote t e) = Prec 1 e <+> symbol ":^:" <+> ansiP t
  ansiP (Cast t e) = Prec 1 e <+> symbol ":::" <+> ansiP t

instance PrettyAnsi FunNote where
  ansiP NoInline = empty
  ansiP InlineMe = comment "{-# INLINE #-}" <+> empty
  ansiP MacroCall = comment "{-# FNMACRO #-}" <+> empty
  ansiP InlinePlease = comment "inline" <+> empty

instance (PrettyAnsi b) => PrettyAnsi (Type t b) where
  ansiP (TVar v) = tF v
  ansiP (TVarBang v) = tF v L.<> typesymbol "!"
  ansiP (TVarUnboxed v) = typesymbol "#" <> tF v
  ansiP (TPrim pt) = ansiP pt
  ansiP (TString) = typename "String"
  ansiP (TUnit) = typename "()"
  ansiP (TProduct t1 t2) = tupled (map ansiP [t1, t2])
  ansiP (TSum alts) = variant (map (\(n,(t,b)) -> tagname n L.<> takenF b <+> ansiP t) alts)
  ansiP (TFun t1 t2) = vT' t1 <+> typesymbol "->" <+> ansiP t2
     where vT' e@(TFun {}) = parens (ansiP e)
           vT' e           = ansiP e
  ansiP (TRecord rp fs s) = ansiP rp <+> record (map (\(f,(t,b)) -> fieldname f <+> symbol ":" L.<> takenF b <+> ansiP t) fs)
                          <> ansiP s
  ansiP (TCon tn [] s) = typename tn <> ansiP s
  ansiP (TCon tn ts s) = typename tn <> ansiP s <+> hsep (map (parens . ) ts)
  ansiP (TSyn tn [] s r) = typename tn <> ansiP s <> (if r then typesymbol "!" else empty)
  ansiP (TSyn tn ts s r) = typename tn <> ansiP s <> (if r then typesymbol "!" else empty)
                            <+> hsep (map (parens . ) ts)
  ansiP (TRPar v m) = keyword "rec" <+> typevar v
#ifdef BUILTIN_ARRAYS
  ansiP (TArray t l s mhole) = (ansiP t <> brackets (ansiP l) <+> ansiP s) &
    (case mhole of Nothing -> id; Just hole -> (<+> keyword "take" <+> parens (ansiP hole)))
#endif
#ifdef REFINEMENT_TYPES
  ansiP (TRefine t p) = braces (ansiP t <+> symbol "|" <+> ansiP p)
#endif

takenF :: Bool -> Doc AnsiStyle
takenF True  = symbol "*"
takenF False = empty

#ifdef BUILTIN_ARRAYS
instance (PrettyAnsi b) => PrettyAnsi (LExpr t b) where
  ansiP (LOp opr [a,b])
     | LeftAssoc  l <- associativity opr = Prec (l+1) a <+> primop opr <+> prettyPrec l b
     | RightAssoc l <- associativity opr = Prec l a <+> primop opr <+> prettyPrec (l+1)  b
     | NoAssoc    l <- associativity opr = Prec l a <+> primop opr <+> prettyPrec l  b
  ansiP (LOp opr [e]) = primop opr <+> Prec 1 e
  ansiP (LOp opr es)  = primop opr <+> tupled (map ansiP es)
  ansiP (LILit i pt) = literal (string $ show i) <+> symbol "::" <+> ansiP pt
  ansiP (LSLit s) = literal $ string s
  ansiP (LVariable x) = ansiP (snd x) L.<> angles (L.int . natToInt $ fst x)
  ansiP (LFun fn ts ls) = funname (unCoreFunName fn) <+> ansiP ts <+> ansiP ls
  ansiP (LApp a b) = Prec 2 a <+> prettyPrec 1 b
  ansiP (LLet a e1 e2) = align (keyword "let" <+> ansiP a <+> symbol "=" <+> ansiP e1 `vsep2`
                                keyword "in" <+> ansiP e2)
  ansiP (LLetBang bs a e1 e2) = align (keyword "let!" <+> tupled (map (L.int . natToInt . fst) bs) <+> ansiP a <+> symbol "=" <+> ansiP e1 `vsep2`
                                       keyword "in" <+> ansiP e2)
  ansiP (LUnit) = tupled []
  ansiP (LTuple e1 e2) = tupled (map ansiP [e1, e2])
  ansiP (LStruct fs) = symbol "#" L.<> record (map (\(n,e) -> fieldname n <+> symbol "=" <+> ansiP e) fs)
  ansiP (LCon tn e t) = parens (tagname tn <+> Prec 1 e) <+> symbol "::" <+> ansiP t
  ansiP (LIf c t e) = group . align $ (keyword "if" <+> ansiP c
                                       `vsep2` indent (keyword "then" </> align (ansiP t))
                                       `vsep2` indent (keyword "else" </> align (ansiP e)))
  ansiP (LCase e tn (v1,a1) (v2,a2)) = align (keyword "case" <+> ansiP e <+> keyword "of"
                                               `vsep2` indent (tagname tn <+> ansiP v1 <+> symbol "->" <+> align (ansiP a1))
                                               `vsep2` indent (ansiP v2 <+> symbol "->" <+> align (ansiP a2)))
  ansiP (LEsac e) = keyword "esac" <+> parens (ansiP e)
  ansiP (LSplit (v1,v2) e1 e2) = align (keyword "split" <+> parens (ansiP v1 <> comma <> ansiP v2) <+> symbol "=" <+> ansiP e1 `vsep2`
                                  keyword "in" <+> ansiP e2)
  ansiP (LMember x f) = Prec 1 x L.<> symbol "." L.<> fieldIndex f
  ansiP (LTake (a,b) rec f e) = align (keyword "take" <+> tupled [ansiP a, ansiP b] <+> symbol "="
                                                      <+> Prec 1 rec <+> record (fieldIndex f:[]) `vsep2`
                                       keyword "in" <+> ansiP e)
  ansiP (LPut rec f v) = Prec 1 rec <+> record [fieldIndex f <+> symbol "=" <+> ansiP v]
  ansiP (LPromote t e) = Prec 1 e <+> symbol ":^:" <+> ansiP t
  ansiP (LCast t e) = Prec 1 e <+> symbol ":::" <+> ansiP t
#endif


#if __GLASGOW_HASKELL__ < 709
instance PrettyAnsi (TyVarName, Kind) where
#else
instance {-# OVERLAPPING #-} PrettyAnsi (TyVarName, Kind) where
#endif
  ansiP (v,k) = ansiP v L.<> typesymbol ":<" L.<> ansiP k

instance PrettyAnsi a => PrettyAnsi (Vec t a) where
  ansiP Nil = empty
  ansiP (Cons x Nil) = ansiP x
  ansiP (Cons x xs) = ansiP x L.<> string "," <+> ansiP xs

instance (PrettyAnsi a, PrettyAnsi b) => PrettyAnsi (Definition e a b) where
  ansiP (FunDef _ fn ts ls t rt e) = funname fn <+> symbol ":" <+> brackets (ansiP ts) <+> braces (ansiP ls) L.<> symbol "." <+>
                                      parens (ansiP t) <+> symbol "->" <+> parens (ansiP rt) <+> symbol "=" `vsep2`
                                      ansiP e
  ansiP (AbsDecl _ fn ts ls t rt) = funname fn <+> symbol ":" <+> brackets (ansiP ts) <+> braces (ansiP ls) L.<> symbol "." <+>
                                     parens (ansiP t) <+> symbol "->" <+> parens (ansiP rt)
  ansiP (TypeDef tn ts Nothing) = keyword "type" <+> typename tn <+> ansiP ts
  ansiP (TypeDef tn ts (Just t)) = keyword "type" <+> typename tn <+> ansiP ts <+>
                                    symbol "=" <+> ansiP t


