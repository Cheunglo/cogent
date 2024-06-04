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

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-missing-signatures #-}

module Cogent.PrettyPrint where
import qualified Cogent.Common.Syntax as S (associativity)
import Cogent.Common.Syntax hiding (associativity)
import Cogent.Common.Types
import Cogent.Compiler
import Cogent.Reorganizer (ReorganizeError(..), SourceObject(..))
import Cogent.Surface
-- import Cogent.TypeCheck --hiding (context)
import Cogent.TypeCheck.Base
import Cogent.TypeCheck.Subst hiding (null)
import qualified Cogent.TypeCheck.ARow as ARow
import qualified Cogent.TypeCheck.Row as Row

import Cogent.Dargent.Allocation
import Cogent.Dargent.Core
import Cogent.Dargent.TypeCheck
import Cogent.Dargent.Util

import Control.Arrow (second)
import Data.Bifoldable (bifoldMap)
import qualified Data.Foldable as F
import Data.Function ((&))
import Data.IntMap as I (IntMap, toList, lookup)
import Data.List (intercalate, nub, partition)
import qualified Data.Map as M hiding (foldr)
#if __GLASGOW_HASKELL__ < 709
import Data.Monoid (mconcat)
import Prelude hiding (foldr)
#else
import Prelude hiding ((<$>), foldr)
#endif
import Data.Nat (natToInt)
import Data.Word (Word32)
import System.FilePath (takeFileName)
import Text.Parsec.Pos
--import Text.PrettyPrint.ANSI.Leijen hiding (indent, tupled)
import Prettyprinter hiding (indent, tupled)
import Prettyprinter.Render.Terminal
import Isabelle.PrettyAnsi
import qualified Data.Set as S


-- pretty-printing theme definition
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

-- meta-level constructs

positionP = string
position = string
errP = string
err = red . string
errbdP = errP
errbd = annBf . err
warnP = string
warn = dullyellow . string
commentP = string
comment = black . string
contextP = string
context = black . string
contextP' = string
context' = string

-- language ast

varname = string
letbangvar = dullgreen . string
primop = blue . string
keyword = annBf . string
literal = dullcyan
reprname = dullcyan . string
typevar = blue . string
typename = blue . annBf . string
typesymbol = cyan . string  -- type operators, e.g. !, ->, take
funname = green . string
funname' = annUl . green . string
fieldname = magenta . string
tagname = dullmagenta . string
dlvarname = dullblue . string
symbol = string
kindsig = red . string
typeargs [] = brackets empty
typeargs xs = encloseSep lbracket rbracket (comma <> space) xs
layoutargs [] = braces $ braces empty
layoutargs xs = encloseSep (lbrace <> lbrace) (rbrace <> rbrace) (comma <> space) xs
array = encloseSep lbracket rbracket (comma <> space)
record = encloseSep (lbrace <> space) (space <> rbrace) (comma <> space)
variant = encloseSep (langle <> space) rangle (symbol "|" <> space) . map (<> space)
reftype v t e = lbracket <+> v <+> symbol ":" <+> t <+> symbol "|" <+> e <+> rbracket

-- combinators, helpers

indentation :: Int
indentation = 3

indent = nest indentation
indent' = (string (replicate indentation ' ') <>) . indent

-- FIXME: no spaces within parens where elements are on multiple lines / zilinc
tupled = __fixme . encloseSep lparen rparen (comma <> space)
-- non-unit tuples. put parens subject to arity
tupled1 [x] = x
tupled1 x = __fixme $ encloseSep lparen rparen (comma <> space) x

spaceList = encloseSep empty empty space
commaList = encloseSep empty empty (comma <> space)


-- associativity
-- ~~~~~~~~~~~~~~~~

associativity :: String -> Associativity
associativity = S.associativity . symbolOp


-- type classes and instances for different constructs
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

class Prec a where  -- precedence
  prec :: a -> Int  -- smaller the number stronger the associativity

instance Prec () where
  prec _ = 0

instance Prec Associativity where
  prec (LeftAssoc  i) = i
  prec (RightAssoc i) = i
  prec (NoAssoc    i) = i
  prec (Prefix)       = 9  -- as in the expression builder

instance Prec (Expr t p ip l e) where
  -- vvv terms
  prec (Var {}) = 0
  prec (TLApp {}) = 0
  prec (BoolLit {}) = 0
  prec (Con _ []) = 0
  prec (IntLit {}) = 0
  prec (CharLit {}) = 0
  prec (StringLit {}) = 0
  prec (Unitel) = 0
  prec (Tuple {}) = 0
#ifdef BUILTIN_ARRAYS
  prec (ArrayLit {}) = 0
  prec (ArrayMap2 {}) = 9
#endif
  prec (UnboxedRecord {}) = 0
  -- vvv parsed by the expression builder
  prec (Member {}) = 8
  prec (Upcast {}) = 9
  prec (App  _ _ False) = 9
  prec (AppC {}) = 9
  prec (Con _ _) = 9
  prec (Put {}) = 9
#ifdef BUILTIN_ARRAYS
  prec (ArrayIndex {}) = 10
  prec (ArrayPut {}) = 9
#endif
  prec (Comp {}) = 10
  prec (PrimOp n _) = prec (associativity n)  -- range 11 - 19
  prec (Annot {}) = 30
  prec (App  _ _ True) = 31
  -- vvv expressions
  prec (Lam  {}) = 100
  prec (LamC {}) = 100
  prec (Seq {}) = 100
  prec (Match {}) = 100
  prec (If {}) = 100
  prec (MultiWayIf {}) = 100
  prec (Let {}) = 100

instance Prec RawExpr where
  prec (RE e) = prec e

instance Prec LocExpr where
  prec (LocExpr _ e) = prec e

instance Prec (TExpr t l) where
  prec (TE _ e _) = prec e

instance Prec (SExpr t l) where
  prec (SE _ e) = prec e
  prec (SU {}) = 0

-- NOTE: they differ from the definition of the fixity of Constraint
instance Prec Constraint where
  prec (_ :&  _) = 3
  prec (_ :@  _) = 2
#ifdef BUILTIN_ARRAYS
  prec (_ :-> _) = 1
#endif
  prec _ = 0

-- ------------------------------------

-- add parens and indents to expressions depending on level
prettyPrec :: (PrettyAnsi a, Prec a) => Int -> a -> Doc AnsiStyle
prettyPrec l x | prec x < l = ansiP x
               | otherwise  = parens (indent (ansiP x))

-- ------------------------------------

class ExprType a where
  isVar :: a -> VarName -> Bool

instance ExprType (Expr t p ip l e) where
  isVar (Var n) s = (n == s)
  isVar _ _ = False

instance ExprType RawExpr where
  isVar (RE e) = isVar e

instance ExprType LocExpr where
  isVar (LocExpr _ e) = isVar e

instance ExprType (TExpr t l) where
  isVar (TE _ e _) = isVar e

instance ExprType (SExpr t l) where
  isVar (SE _ e) = isVar e
  isVar (SU {}) = const False

-- ------------------------------------

class PatnType a where
  isPVar  :: a -> VarName -> Bool
  prettyP :: a -> Doc AnsiStyle
  prettyB :: (PrettyAnsi t, PrettyAnsi e, Prec e) => (a, Maybe t, e) -> Bool -> Doc AnsiStyle  -- binding

instance (PrettyName pv, PatnType ip, PrettyAnsi ip, PrettyAnsi e) => PatnType (IrrefutablePattern pv ip e) where
  isPVar (PVar pv) = isName pv
  isPVar _ = const False

  prettyP p@(PTake {}) = parens (ansiP p)
  prettyP p = ansiP p

  prettyB (p, Just t, e) i
    = group (ansiP p <+> symbol ":" <+> ansiP t <+> symbol "=" <+>
             (if i then (prettyPrec 100) else ansiP) e)
  prettyB (p, Nothing, e) i
    = group (ansiP p <+> symbol "=" <+>
             (if i then (prettyPrec 100) else ansiP) e)

instance PatnType RawIrrefPatn where
  isPVar  (RIP p) = isPVar p
  prettyP (RIP p) = prettyP p
  prettyB (RIP p,mt,e) = prettyB (p,mt,e)

instance PatnType LocIrrefPatn where
  isPVar  (LocIrrefPatn _ p) = isPVar p
  prettyP (LocIrrefPatn _ p) = prettyP p
  prettyB (LocIrrefPatn _ p,mt,e) = prettyB (p,mt,e)

instance (PrettyAnsi t, PrettyAnsi l) => PatnType (TIrrefPatn t l) where
  isPVar  (TIP p _) = isPVar p
  prettyP (TIP p _) = prettyP p
  prettyB (TIP p _,mt,e) = prettyB (p,mt,e)

instance (PatnType ip, PrettyAnsi ip) => PatnType (Pattern ip) where
  isPVar (PIrrefutable ip) = isPVar ip
  isPVar _ = const False

  prettyP (PIrrefutable ip) = prettyP ip
  prettyP p = ansiP p

  prettyB (p, Just t, e) i
       = group (ansiP p <+> symbol ":" <+> ansiP t <+> symbol "<=" <+> (if i then (prettyPrec 100) else ansiP) e)
  prettyB (p, Nothing, e) i
       = group (ansiP p <+> symbol "<=" <+> (if i then (prettyPrec 100) else ansiP) e)

instance PatnType RawPatn where
  isPVar  (RP p)= isPVar p
  prettyP (RP p) = prettyP p
  prettyB (RP p,mt,e) = prettyB (p,mt,e)

instance PatnType LocPatn where
  isPVar  (LocPatn _ p) = isPVar p
  prettyP (LocPatn _ p) = prettyP p
  prettyB (LocPatn _ p,mt,e) = prettyB (p,mt,e)

instance (PrettyAnsi t, PrettyAnsi l) => PatnType (TPatn t l) where
  isPVar  (TP p _) = isPVar p
  prettyP (TP p _) = prettyP p
  prettyB (TP p _,mt,e) = prettyB (p,mt,e)

-- ------------------------------------

class TypeType t where
  isCon :: t -> Bool
  isTakePut :: t -> Bool
  isFun :: t -> Bool
  isAtomic :: t -> Bool

instance TypeType (Type e l t) where
  isCon     (TCon {})  = True
  isCon     _          = False
  isFun     (TFun {})  = True
  isFun     _          = False
  isTakePut (TTake {}) = True
  isTakePut (TPut  {}) = True
#ifdef BUILTIN_ARRAYS
  isTakePut (TATake {}) = True
  isTakePut (TAPut  {}) = True
#endif
  isTakePut _          = False
  isAtomic t | isFun t || isTakePut t = False
             | TCon _ (_:_) _ <- t = False
             | TUnbox _ <- t = False
             | TBang  _ <- t= False
             | otherwise = True

instance TypeType RawType where
  isCon     (RT t) = isCon     t
  isTakePut (RT t) = isTakePut t
  isFun     (RT t) = isFun     t
  isAtomic  (RT t) = isAtomic  t

instance TypeType DepType where
  isCon     (DT t) = isCon     t
  isTakePut (DT t) = isTakePut t
  isFun     (DT t) = isFun     t
  isAtomic  (DT t) = isAtomic  t

instance TypeType TCType where
  isCon     (T t) = isCon t
  isCon     _     = False
  isFun     (T t) = isFun t
  isFun     _     = False
  isTakePut (T t) = isTakePut t
  isTakePut _     = False
  isAtomic  (T t) = isAtomic t
  isAtomic  (U _) = True
  isAtomic  (Synonym _ []) = True
  isAtomic  _     = False

-- ------------------------------------

class PrettyName a where
  prettyName :: a -> Doc AnsiStyle
  isName :: a -> String -> Bool

instance PrettyName VarName where
  prettyName = varname
  isName s = (== s)

instance PrettyAnsi t => PrettyName (VarName, t) where
  prettyName (a, b) | __cogent_fshow_types_in_pretty = parens $ prettyName a <+> comment "::" <+> ansiP b
                    | otherwise = prettyName a
  isName (a, b) x = a == x

-- ------------------------------------

-- class Pretty

instance PrettyAnsi Likelihood where
  ansiP Likely   = symbol "=>"
  ansiP Unlikely = symbol "~>"
  ansiP Regular  = symbol "->"

instance (PrettyName pv, PatnType ip, PrettyAnsi ip, PrettyAnsi e) => PrettyAnsi (IrrefutablePattern pv ip e) where
  ansiP (PVar v) = prettyName v
  ansiP (PTuple ps) = tupled (map ansiP ps)
  ansiP (PUnboxedRecord fs) = string "#" <> record (fmap handleTakeAssign fs)
  ansiP (PUnderscore) = symbol "_"
  ansiP (PUnitel) = string "()"
  ansiP (PTake v fs) = prettyName v <+> record (fmap handleTakeAssign fs)
#ifdef BUILTIN_ARRAYS
  ansiP (PArray ps) = array $ map ansiP ps
  ansiP (PArrayTake v ips) = prettyName v <+> string "@" <>
                              record (map (\(i,p) -> symbol "@" <> ansiP i <+> symbol "=" <+> ansiP p) ips)
#endif

instance PrettyAnsi RawIrrefPatn where
  ansiP (RIP ip) = ansiP ip

instance PrettyAnsi LocIrrefPatn where
  ansiP (LocIrrefPatn _ ip) = ansiP ip

instance (PrettyAnsi t, PrettyAnsi l) => PrettyAnsi (TIrrefPatn t l) where
  ansiP (TIP ip _) = ansiP ip

instance (PatnType ip, PrettyAnsi ip) => PrettyAnsi (Pattern ip) where
  ansiP (PCon c [] )     = tagname c
  ansiP (PCon c [p])     = tagname c <+> prettyP p
  ansiP (PCon c ps )     = tagname c <+> spaceList (map prettyP ps)
  ansiP (PIntLit i)      = literal (string $ show i)
  ansiP (PBoolLit b)     = literal (string $ show b)
  ansiP (PCharLit c)     = literal (string $ show c)
  ansiP (PIrrefutable p) = ansiP p

instance PrettyAnsi RawPatn where
  ansiP (RP p) = ansiP p

instance PrettyAnsi LocPatn where
  ansiP (LocPatn _ p) = ansiP p

instance (PrettyAnsi t, PrettyAnsi l) => PrettyAnsi (TPatn t l) where
  ansiP (TP p _) = ansiP p

instance (PrettyAnsi t, PatnType ip, PatnType p, PrettyAnsi p, PrettyAnsi e, Prec e) => PrettyAnsi (Binding t p ip e) where
  ansiP (Binding p t e []) = prettyB (p,t,e) False
  ansiP (Binding p t e bs)
     = prettyB (p,t,e) True <+> hsep (map (letbangvar . ('!':)) bs)
  ansiP (BindingAlts p t e [] alts) = prettyB (p,t,e) False
                                    <> mconcat (map ((hardline <>) . indent . prettyA True) alts)
  ansiP (BindingAlts p t e bs alts) = prettyB (p,t,e) True <+> hsep (map (letbangvar . ('!':)) bs)
                                    <> mconcat (map ((hardline <>) . indent . prettyA True) alts)

instance (PrettyAnsi p, PrettyAnsi e) => PrettyAnsi (Alt p e) where
  ansiP (Alt p arrow e) = ansiP p <+> group (ansiP arrow <+> ansiP e)

prettyA :: (PrettyAnsi p, PrettyAnsi e)
        => Bool  -- is biased
        -> Alt p e
        -> Doc AnsiStyle
prettyA False alt = symbol "|" <+> ansiP alt
prettyA True alt = symbol "|>" <+> ansiP alt

instance PrettyAnsi Inline where
  ansiP Inline = keyword "inline" <+> empty
  ansiP NoInline = empty

instance (ExprType e, Prec e, PrettyAnsi t, PatnType p, PrettyAnsi p, PatnType ip, PrettyAnsi ip, PrettyAnsi e, PrettyAnsi l) =>
         PrettyAnsi (Expr t p ip l e) where
  ansiP (Var x)             = varname x
  ansiP (TLApp x ts ls note) = ansiP note <> varname x
                                  <> typeargs (map (\case Nothing -> symbol "_"; Just t -> ansiP t) ts)
                                  <> layoutargs (map (\case Nothing -> symbol "_"; Just t -> ansiP t) ls)
  ansiP (Member x f)        = prettyPrec 9 x <> symbol "." <> fieldname f
  ansiP (IntLit i)          = literal (string $ show i)
  ansiP (BoolLit b)         = literal (string $ show b)
  ansiP (CharLit c)         = literal (string $ show c)
  ansiP (StringLit s)       = literal (string $ show s)
#ifdef BUILTIN_ARRAYS
  ansiP (ArrayLit es)       = array $ map ansiP es
  ansiP (ArrayIndex e i)    = prettyPrec 11 e <+> symbol "@" <+> prettyPrec 10 i
  ansiP (ArrayMap2 ((p1,p2),f) (e1,e2)) = keyword "map2"
                                       <+> parens (string "\\" <> ansiP p1 <+> ansiP p2 <+> symbol "=>" <+> ansiP f)
                                       <+> prettyPrec 1 e1 <+> prettyPrec 1 e2
  ansiP (ArrayPut e es)     = prettyPrec 10 e <+> symbol "@"
                            <> record (map (\(i,e) -> symbol "@" <> ansiP i <+> symbol "=" <+> ansiP e) es)
#endif
  ansiP (Unitel)            = string "()"
  ansiP (PrimOp n [a,b])
     | LeftAssoc  l <- associativity n = prettyPrec (l+1) a <+> primop n <+> prettyPrec l     b
     | RightAssoc l <- associativity n = prettyPrec l     a <+> primop n <+> prettyPrec (l+1) b
     | NoAssoc    l <- associativity n = prettyPrec l     a <+> primop n <+> prettyPrec l     b
  ansiP (PrimOp n [e])
     | a  <- associativity n = primop n <+> prettyPrec (prec a) e
  ansiP (PrimOp n es)       = primop n <+> tupled (map ansiP es)
  ansiP (Upcast e)          = keyword "upcast" <+> prettyPrec 9 e
  ansiP (Lam p mt e)        = string "\\" <> ansiP p <>
                               (case mt of Nothing -> empty; Just t -> space <> symbol ":" <+> ansiP t) <+> symbol "=>" <+> prettyPrec 101 e
  ansiP (LamC p mt e _)     = ansiP (Lam p mt e :: Expr t p ip l e)
  ansiP (App  a b False)    = prettyPrec 10 a <+> prettyPrec 9 b
  ansiP (App  a b True )    = prettyPrec 31 a <+> symbol "$" <+> prettyPrec 32 b
  ansiP (Comp f g)          = prettyPrec 10 f <+> symbol "o" <+> prettyPrec 9 g
  ansiP (AppC a b)          = prettyPrec 10 a <+> prettyPrec 9 b
  ansiP (Con n [] )         = tagname n
  ansiP (Con n es )         = tagname n <+> spaceList (map (prettyPrec 9) es)
  ansiP (Tuple es)          = tupled (map ansiP es)
  ansiP (UnboxedRecord fs)  = string "#" <> record (map (handlePutAssign . Just) fs)
  ansiP (If c vs t e)       = group (keyword "if" <+> handleBangedIf vs (prettyPrec 100 c)
                                                   `vsep2` indent (keyword "then" `fillSep2` ansiP t)
                                                   `vsep2` indent (keyword "else" `fillSep2` ansiP e))
    where handleBangedIf []  = id
          handleBangedIf vs  = (<+> hsep (map (letbangvar . ('!':)) vs))
  ansiP (MultiWayIf es el)  = keyword "if" <+> mconcat (map ((hardline <>) . indent . (symbol "|" <+>) . prettyBranch) es)
                                            <> hardline <> indent (symbol "|" <+> keyword "else" <+> symbol "->" <+> ansiP el)
    where handleBangedIf []  = id
          handleBangedIf vs  = (<+> hsep (map (letbangvar . ('!':)) vs))

          prettyBranch (c,bs,l,e) = handleBangedIf bs (prettyPrec 100 c) <+> ansiP l <+> ansiP e
  ansiP (Match e [] alts)   = prettyPrec 100 e
                               <> mconcat (map ((hardline <>) . indent . prettyA False) alts)
  -- vvv It's a hack here. See the notes in <tests/pass_letbang-cond-type-annot.cogent>
  ansiP (Match e bs alts)   = handleLetBangs bs (prettyPrec 30 e)
                               <> mconcat (map ((hardline <>) . indent . prettyA False) alts)
    where handleLetBangs bs  = (<+> hsep (map (letbangvar . ('!':)) bs))
  ansiP (Seq a b)           = prettyPrec 100 a <> symbol ";" `vsep2` ansiP b
  ansiP (Let []     e)      = __impossible "ansiP (in RawExpr)"
  ansiP (Let (b:[]) e)      = keyword "let" <+> indent (ansiP b)
                                             `vsep2` keyword "in" <+> indent (ansiP e)
  ansiP (Let (b:bs) e)      = keyword "let" <+> indent (ansiP b)
                                             `vsep2` vsep (map ((keyword "and" <+>) . indent . ansiP) bs)
                                             `vsep2` keyword "in" <+> indent (ansiP e)
  ansiP (Put e fs)          = prettyPrec 10 e <+> record (map handlePutAssign fs)
  ansiP (Annot e t)         = prettyPrec 31 e <+> symbol ":" <+> ansiP t

instance PrettyAnsi RawExpr where
  ansiP (RE e) = ansiP e

instance PrettyAnsi LocExpr where
  ansiP (LocExpr _ e) = ansiP e

instance (PrettyAnsi t, PrettyAnsi l) => PrettyAnsi (TExpr t l) where
  ansiP (TE t e _) | __cogent_fshow_types_in_pretty = parens $ ansiP e <+> comment "::" <+> ansiP t
                    | otherwise = ansiP e

instance (PrettyAnsi t, PrettyAnsi l) => PrettyAnsi (SExpr t l) where
  ansiP (SE t e) | __cogent_fshow_types_in_pretty = parens $ ansiP e <+> comment "::" <+> ansiP t
                  | otherwise = ansiP e
  ansiP (SU t n) | __cogent_fshow_types_in_pretty = parens $ warn ('?':show n) <+> comment "::" <+> ansiP t
                  | otherwise = warn ('?':show n)

instance PrettyAnsi RecursiveParameter where
  ansiP (Rec p) = typesymbol "rec" <+> symbol p
  ansiP NonRec  = empty

prettyT' :: (TypeType t, PrettyAnsi t) => t -> Doc AnsiStyle
prettyT' t | not $ isAtomic t = parens (ansiP t)
           | otherwise        = ansiP t

instance (PrettyAnsi t, TypeType t, PrettyAnsi e, PrettyAnsi l, Eq l) => PrettyAnsi (Type e l t) where
  ansiP (TCon n [] s) = (if | readonly s -> (<> typesymbol "!")
                             | s == Unboxed && n `notElem` primTypeCons -> (typesymbol "#" <>)
                             | otherwise -> id) . (case s of Boxed _ (Just l) -> (<+> typesymbol "layout" <+> ansiP l); _ -> id) $ typename n
  ansiP (TCon n as s) = (if | readonly s -> (<> typesymbol "!") . parens
                             | s == Unboxed -> ((typesymbol "#" <>) . parens)
                             | otherwise -> id) . (case s of Boxed _ (Just l) -> (<+> typesymbol "layout" <+> ansiP l); _ -> id) $
                         typename n <+> hsep (map prettyT' as)
  ansiP (TVar n b u) = (if u then typesymbol "#" else empty) <> typevar n <> (if b then typesymbol "!" else empty)
  ansiP (TTuple ts) = tupled (map ansiP ts)
  ansiP (TUnit)     = typesymbol "()" & (if __cogent_fdisambiguate_pp then (<+> comment "{- unit -}") else id)
#ifdef BUILTIN_ARRAYS
  ansiP (TArray t l s tkns) =
    let (sigilPretty, layoutPretty) = case s of
          Unboxed     -> ((typesymbol "#" <>), id)
          Boxed ro ml -> (if ro then (<> typesymbol "!") else id, case ml of Just l -> (<+> typesymbol "layout" <+> ansiP l); _ -> id)
        (takes,puts) = partition snd tkns
        pTakens = if null takes then id else
                (<+> typesymbol "@take" <+> tupled (map (ansiP . fst) takes))
        pPuts = id  -- default is put
        -- pPuts   = if null puts  then id else
        --         (<+> typesymbol "@put"  <+> tupled (map (ansiP . fst) puts ))
     in prettyT' t <> (layoutPretty . sigilPretty $ brackets (ansiP l)) & (pPuts . pTakens)
  ansiP (TATake idxs t)
    = (prettyT' t <+> typesymbol "@take"
                  <+> tupled (map ansiP idxs))
      & (if __cogent_fdisambiguate_pp then (<+> comment "{- @take -}") else id)
  ansiP (TAPut  idxs t)
    = (prettyT' t <+> typesymbol "@put"
                  <+> tupled (map ansiP idxs))
      & (if __cogent_fdisambiguate_pp then (<+> comment "{- @put -}") else id)
#endif
#ifdef REFINEMENT_TYPES
  ansiP (TRefine v t e) = reftype (varname v) (ansiP t) (ansiP e)
#endif
  ansiP (TRecord rp ts s) =
      let recordPretty = record (map (\(a,(b,c)) -> fieldname a <+> symbol ":" <+> ansiP b) ts) -- all untaken
          tk = map fst $ filter (snd . snd) ts
          tkUntkPretty = (if or $ map (snd . snd) ts
                          then (<+> typesymbol "take" <+> tupled1 (map fieldname tk))
                          else id)
          (sigilPretty, layoutPretty) = case s of
            Unboxed     -> ((typesymbol "#" <>), id)
            Boxed rw ml -> (if rw then (<> typesymbol "!") else id, case ml of Just l -> (<+> typesymbol "layout" <+> ansiP l); _ -> id)
       in ansiP rp <+> (layoutPretty . tkUntkPretty . sigilPretty $ recordPretty)
  ansiP (TVariant ts) | any snd ts = let
     names = map fst $ filter (snd . snd) $ M.toList ts
   in ansiP (TVariant $ fmap (second (const False)) ts :: Type e l t)
        <+> typesymbol "take"
        <+> tupled1 (map fieldname names)
  ansiP (TVariant ts) = variant (map (\(a,bs) -> case bs of
                                          [] -> tagname a
                                          _  -> tagname a <+> spaceList (map prettyT' bs)) $ M.toList (fmap fst ts))
  ansiP (TFun t t') = prettyT' t <+> typesymbol "->" <+> prettyT' t'
    where prettyT' e | isFun e   = parens (ansiP e)
                     | otherwise = ansiP e
  ansiP (TUnbox t) = (typesymbol "#" <> prettyT' t) & (if __cogent_fdisambiguate_pp then (<+> comment "{- unbox -}") else id)
  ansiP (TBang t) = (prettyT' t <> typesymbol "!") & (if __cogent_fdisambiguate_pp then (<+> comment "{- bang -}") else id)
  ansiP (TRPar v b m) = (if __cogent_fdisambiguate_pp then (comment "{- rec -}" <+> ) else id) $ typevar v <> (if b then typesymbol "!" else mempty)
  ansiP (TTake fs x) = (prettyT' x <+> typesymbol "take"
                                    <+> case fs of Nothing  -> tupled (fieldname ".." : [])
                                                   Just fs' -> tupled1 (map fieldname fs'))
                        & (if __cogent_fdisambiguate_pp then (<+> comment "{- take -}") else id)
  ansiP (TPut fs x) = (prettyT' x <+> typesymbol "put"
                                   <+> case fs of Nothing -> tupled (fieldname ".." : [])
                                                  Just fs' -> tupled1 (map fieldname fs'))
                       & (if __cogent_fdisambiguate_pp then (<+> comment "{- put -}") else id)
  ansiP (TLayout l t) = (prettyT' t <+> typesymbol "layout" <+> ansiP l)
           & (if __cogent_fdisambiguate_pp then (<+> comment "{- layout -}") else id)

instance PrettyAnsi RawType where
  ansiP (RT t) = ansiP t

instance PrettyAnsi DepType where
  ansiP (DT t) = ansiP t

instance PrettyAnsi TCType where
  ansiP (T t) = ansiP t
  ansiP t@(V v) = symbol "V" <+> ansiP v
  ansiP t@(R rp v s) =
    let sigilPretty = case s of
                        Left s -> ansiP s
                        Right n -> parens (symbol "?" <> ansiP n)
        rpPretty    = case rp of
                        Mu v -> typesymbol "rec" <+> symbol v <+> empty
                        None -> empty
                        UP p -> parens (symbol "?" <> ansiP p) <+> empty
     in symbol "R" <+> rpPretty <> ansiP v <+> sigilPretty
#ifdef BUILTIN_ARRAYS
  ansiP (A t l s row) =
    let sigilPretty = case s of
                        Left s -> ansiP s
                        Right n -> parens (warn $ '?' : show n)
        holePretty = case row of
                       Left Nothing  -> empty
                       Left (Just e) -> space <> keyword "@take" <+> parens (ansiP e)
                       Right n       -> space <> warn ('?' : show n)

     in symbol "A" <+> ansiP t <+> brackets (ansiP l) <+> sigilPretty <> holePretty
#endif
  ansiP (U v) = warn ('?':show v)
  ansiP (Synonym n []) = warn ("syn:" ++ n)
  ansiP (Synonym n ts) = warn ("syn:" ++ n) <+> spaceList (map ansiP ts)

instance PrettyAnsi LocType where
  ansiP t = ansiP (stripLocT t)

renderPolytypeHeader vs ts = keyword "all" <> tupled (map prettyKS vs ++ map prettyTS ts) <> symbol "."
    where prettyKS (v,K False False False) = typevar v
          prettyKS (v,k) = typevar v <+> symbol ":<" <+> ansiP k
          prettyTS (v,t) = typevar v <+> symbol ":~" <+> ansiP t

instance PrettyAnsi t => PrettyAnsi (Polytype t) where
  ansiP (PT [] [] t) = ansiP t
  ansiP (PT vs ts t) = renderPolytypeHeader vs ts <+> ansiP t

renderTypeDecHeader n vs = keyword "type" <+> typename n <> hcat (map ((space <>) . typevar) vs)
                                          <+> symbol "="

prettyFunDef :: (PrettyAnsi p, PrettyAnsi e, PrettyAnsi t) => Bool -> FunName -> Polytype t -> [Alt p e] -> Doc AnsiStyle
prettyFunDef typeSigs v pt [Alt p Regular e] = (if typeSigs then (funname v <+> symbol ":" <+> ansiP pt `vsep2`) else id)
                                                 (funname v <+> ansiP p <+> group (indent (symbol "=" `vsep2` ansiP e)))
prettyFunDef typeSigs v pt alts = (if typeSigs then (funname v <+> symbol ":" <+> ansiP pt `vsep2`) else id) $
                                       (indent (funname v <> mconcat (map ((hardline <>) . indent . prettyA False) alts)))

prettyConstDef typeSigs v t e  = (if typeSigs then (funname v <+> symbol ":" <+> ansiP t `vsep2`) else id) $
                                         (funname v <+> group (indent (symbol "=" <+> ansiP e)))

instance (PrettyAnsi t, PrettyAnsi p, PrettyAnsi e) => PrettyAnsi (TopLevel t p e) where
  ansiP (TypeDec n vs t) = keyword "type" <+> typename n <> hcat (map ((space <>) . typevar) vs)
                                           <+> indent (symbol "=" `fillSep2` ansiP t)
  ansiP (RepDef f) = ansiP f
  ansiP (FunDef v pt alts) = prettyFunDef True v pt alts
  ansiP (AbsDec v pt) = funname v <+> symbol ":" <+> ansiP pt
  ansiP (Include s) = keyword "include" <+> literal (string $ show s)
  ansiP (IncludeStd s) = keyword "include <" <+> literal (string $ show s)
  ansiP (AbsTypeDec n vs ts) = keyword "type" <+> typename n  <> hcat (map ((space <>) . typevar) vs)
                             <> (if F.null ts then empty else empty <+> symbol "-:" <+> commaList (map ansiP ts))
  ansiP (ConstDef v t e) = prettyConstDef True v t e
  ansiP (DocBlock _) = __fixme empty  -- FIXME: doesn't PP docs right now

instance PrettyAnsi Kind where
  ansiP k = kindsig (stringFor k)
    where stringFor k = (if canDiscard k then "D" else "")
                     ++ (if canShare   k then "S" else "")
                     ++ (if canEscape  k then "E" else "")

instance PrettyAnsi SourcePos where
  ansiP p | __cogent_ffull_src_path = position (show p)
           | otherwise = position $ show $ setSourceName p (takeFileName $ sourceName p)

instance PrettyAnsi DataLayoutDecl where
  ansiP (DataLayoutDecl _ n v e) = keyword "layout" <+> reprname n <+> hsep (fmap varname v) <+> indent (symbol "=" `fillSep2` ansiP e)

instance PrettyAnsi DataLayoutSize where
  ansiP (Bits b) = literal (string (show b ++ "b"))
  ansiP (Bytes b) = literal (string (show b ++ "B"))
  ansiP (Add a b) = ansiP a <+> symbol "+" <+> ansiP b

instance PrettyAnsi Endianness where
  ansiP LE = keyword "LE"
  ansiP BE = keyword "BE"
  ansiP ME = keyword "ME"

instance PrettyAnsi d => PrettyAnsi (DataLayoutExpr' d) where
  ansiP (RepRef n s) = if null s then reprname n else parens $ reprname n <+> hsep (fmap ansiP s)
  ansiP (Prim sz) = ansiP sz
  ansiP (Offset e s) = ansiP e <+> keyword "at" <+> ansiP s
  ansiP (After e f) = ansiP e <+> keyword "after" <+> ansiP f
  ansiP (Endian e n) = ansiP e <+> keyword "using" <+> ansiP n
  ansiP (Record fs) = keyword "record" <+> record (map (\(f,_,e) -> fieldname f <+> symbol ":" <+> ansiP e ) fs)
  ansiP (Variant e vs) = keyword "variant" <+> parens (ansiP e)
                                                 <+> record (map (\(f,_,i,e) -> tagname f <+> tupled [literal $ string $ show i] <> symbol ":" <+> ansiP e) vs)
#ifdef BUILTIN_ARRAYS
  ansiP (Array e l s) = keyword "array" <+> braces (ansiP e) <+> brackets (ansiP l) <+> keyword "at" <+> ansiP s
#endif
  ansiP Ptr = keyword "pointer"
  ansiP (LVar n) = dlvarname n

instance PrettyAnsi DataLayoutExpr where
  ansiP (DL l) = ansiP l

instance PrettyAnsi TCDataLayout where
  ansiP (TL l) = ansiP l
  ansiP (TLU n) = warn ('?':show n)

instance PrettyAnsi Metadata where
  ansiP (Constant {constName})              = err "the binding" <+> funname constName `vsep2` err "is a global constant"
  ansiP (Reused {varName, boundAt, usedAt}) = err "the variable" <+> varname varName
                                               <+> err "bound at" <+> ansiP boundAt <> err ""
                                               `vsep2` err "was already used at"
                                               `vsep2` indent' (vsep $ map ansiP $ F.toList usedAt)
  ansiP (Unused {varName, boundAt}) = err "the variable" <+> varname varName
                                       <+> err "bound at" <+> ansiP boundAt <> err ""
                                       `vsep2` err "was never used."
  ansiP (UnusedInOtherBranch {varName, boundAt, usedAt}) =
    err "the variable" <+> varname varName
    <+> err "bound at" <+> ansiP boundAt <> err ""
    `vsep2` err "was used in another branch of control at"
    `vsep2` indent' (vsep $ map ansiP $ F.toList usedAt)
    `vsep2` err "but not this one."
  ansiP (UnusedInThisBranch {varName, boundAt, usedAt}) =
    err "the variable" <+> varname varName
    <+> err "bound at" <+> ansiP boundAt <> err ""
    `vsep2` err "was used in this branch of control at"
    `vsep2` indent' (vsep $ map ansiP $ F.toList usedAt)
    `vsep2` err "but not in all other branches."
  ansiP Suppressed = err "a binder for a value of this type is being suppressed."
  ansiP (UsedInMember {fieldName}) = err "the field" <+> fieldname fieldName
                                       <+> err "is being extracted without taking the field in a pattern."
#ifdef BUILTIN_ARRAYS
  ansiP UsedInArrayIndexing = err "an element of the array is being accessed"
  ansiP MultipleArrayTakePut = err "more than one array element is being taken or put"
#endif
  ansiP UsedInLetBang = err "it is being returned from such a context."
  ansiP (TypeParam {functionName, typeVarName }) = err "it is required by the type of" <+> funname functionName
                                                      <+> err "(type variable" <+> typevar typeVarName <+> err ")"
  ansiP ImplicitlyTaken = err "it is implicitly taken via subtyping."
  -- ansiP (LayoutParam exp lv) = err "it is required by the expression" <+> ansiP exp
                            -- <+> err "(layout variable" <+> dlvarname lv <+> err ")"

instance PrettyAnsi FuncOrVar where
  ansiP MustFunc  = err "Function"
  ansiP MustVar   = err "Variable"
  ansiP FuncOrVar = err "Variable or function"

instance PrettyAnsi TypeError where
  ansiP (DifferingNumberOfConArgs f n m) = err "Constructor" <+> tagname f
                                        <+> err "invoked with differing number of arguments (" <> int n <> err " vs " <> int m <> err ")"
  ansiP (DuplicateTypeVariable vs)      = err "Duplicate type variable(s)" <+> commaList (map typevar vs)
  ansiP (SuperfluousTypeVariable vs)    = err "Superfluous type variable(s)" <+> commaList (map typevar vs)
  ansiP (DuplicateLayoutVariable vs)    = err "Duplicate layout variable(s)" <+> commaList (map dlvarname vs)
  ansiP (SuperfluousLayoutVariable vs)  = err "Superfluous layout variable(s)" <+> commaList (map dlvarname vs)
  ansiP (TypeVariableNotDeclared vs)    = err "Type variable(s) not declared" <+> commaList (map typevar vs)
  ansiP (DuplicateRecordFields fs)      = err "Duplicate record field(s)" <+> commaList (map fieldname fs)
  ansiP (FunctionNotFound fn)           = err "Function" <+> funname fn <+> err "not found"
  ansiP (RedefiningPrimType tn)         = err "Redefining primitive type" <+> typename tn
  ansiP (TooManyTypeArguments fn pt)    = err "Too many type arguments to function"
                                           <+> funname fn <+> err "of type" <+> ansiP pt
  ansiP (TooManyLayoutArguments fn pt)  = err "Too many layout arguments to function"
                                           <+> funname fn <+> err "of type" <+> ansiP pt
  ansiP (NotInScope fov vn)             = ansiP fov <+> varname vn <+> err "not in scope"
  ansiP (UnknownTypeVariable vn)        = err "Unknown type variable" <+> typevar vn
  ansiP (UnknownTypeConstructor tn)     = err "Unknown type constructor" <+> typename tn
  ansiP (TypeArgumentMismatch tn provided required)
                                         = typename tn <+> err "expects"
                                           <+> int required <+> err "arguments, but has been given" <+> int provided
  ansiP (TypeMismatch t1 t2)            = err "Mismatch between" `vsep2` indent' (ansiP t1)
                                           `vsep2` err "and" `vsep2` indent' (ansiP t2)
  ansiP (RequiredTakenField f t)        = err "Field" <+> fieldname f <+> err "of type" <+> ansiP t
                                           <+> err "is required, but has been taken"
  ansiP (TypeNotShareable t m)          = err "Cannot share type" <+> ansiP t
                                           `vsep2` err "but this is needed as" <+> ansiP m
  ansiP (TypeNotEscapable t m)          = err "Cannot let type" <+> ansiP t <+> err "escape from a !-ed context,"
  ansiP (TypeNotDiscardable t m)        = err "Cannot discard type" <+> ansiP t
                                           <+> err "but this is needed as" <+> ansiP m
  ansiP (PatternsNotExhaustive t tags)  = err "Patterns not exhaustive for type" <+> ansiP t
                                           `vsep2` err "cases not matched" <+> tupled1 (map tagname tags)
  ansiP (UnsolvedConstraint c os)       = analyseLeftover c os
  ansiP (RecordWildcardsNotSupported)   = err "Record wildcards are not supported"
  ansiP (NotAFunctionType t)            = err "Type" <+> ansiP t <+> err "is not a function type"
  ansiP (DuplicateVariableInPattern vn) = err "Duplicate variable" <+> varname vn <+> err "in pattern"
  -- ansiP (DuplicateVariableInPattern vn pat)       = err "Duplicate variable" <+> varname vn <+> err "in pattern:"
  --                                                    `vsep2` ansiP pat
  -- ansiP (DuplicateVariableInIrrefPattern vn ipat) = err "Duplicate variable" <+> varname vn <+> err "in (irrefutable) pattern:"
  --                                                    `vsep2` ansiP ipat
  ansiP (TakeFromNonRecordOrVariant fs t) = err "Cannot" <+> keyword "take" <+> err "fields"
                                             <+> (case fs of Nothing  -> tupled (fieldname ".." : [])
                                                             Just fs' -> tupled1 (map fieldname fs'))
                                             <+> err "from non record/variant type:"
                                             `vsep2` indent' (ansiP t)
  ansiP (PutToNonRecordOrVariant fs t)    = err "Cannot" <+> keyword "put" <+> err "fields"
                                             <+> (case fs of Nothing  -> tupled (fieldname ".." : [])
                                                             Just fs' -> tupled1 (map fieldname fs'))
                                             <+> err "into non record/variant type:"
                                             `vsep2` indent' (ansiP t)
  ansiP (TakeNonExistingField f t) = err "Cannot" <+> keyword "take" <+> err "non-existing field"
                                      <+> fieldname f <+> err "from record/variant" `vsep2` indent' (ansiP t)
  ansiP (PutNonExistingField f t)  = err "Cannot" <+> keyword "put" <+> err "non-existing field"
                                      <+> fieldname f <+> err "into record/variant" `vsep2` indent' (ansiP t)
  ansiP (DiscardWithoutMatch t)    = err "Variant tag"<+> tagname t <+> err "cannot be discarded without matching on it."
  ansiP (RequiredTakenTag t)       = err "Required variant" <+> tagname t <+> err "but it has already been matched."
#ifdef BUILTIN_ARRAYS
  ansiP (ArithConstraintsUnsatisfiable es msg) = err "The following arithmetic constraints are unsatisfiable" <> colon
                                              `vsep2` indent' (vsep (map ((<> semi) . ansiP) es))
                                              `vsep2` err "The SMT-solver comments" <> colon
                                              `vsep2` indent' (ansiP msg)
  ansiP (TakeElementsFromNonArrayType is t) = err "Taking elements" <+> commaList (map ansiP is)
                                           `vsep2` err "from a non-array type" <+> ansiP t
  ansiP (PutElementsToNonArrayType is t)    = err "Putting elements" <+> commaList (map ansiP is)
                                           `vsep2` err "to a non-array type" <+> ansiP t
#endif
  ansiP (CustTyGenIsSynonym t)     = err "Type synonyms have to be fully expanded in --cust-ty-gen file:" `vsep2` indent' (ansiP t)
  ansiP (CustTyGenIsPolymorphic t) = err "Polymorphic types are not allowed in --cust-ty-gen file:" `vsep2` indent' (ansiP t)
  ansiP (DataLayoutError e)        = err "Data Layout Error:" `vsep2` indent' (ansiP e)
  ansiP (LayoutOnNonRecordOrCon t) = err "Tried to put a layout onto something that isn't a record or abstract type:" `vsep2` indent' (ansiP t)
  ansiP (LayoutDoesNotMatchType l t) = err "Layout " `vcat2` indent' (ansiP l)
                                          `vcat2` err " does not match type " `vcat2` indent' (ansiP t)
  ansiP (LayoutsNotCompatible l1 l2) = err "Layout " `vcat2` indent' (ansiP l1)
                                          `vcat2` err " is not compatible with layout " `vcat2` indent' (ansiP l2)
  ansiP (TypesNotFit t1 t2)          = err "The layout of type " `vcat2` indent' (ansiP t1)
                                          `vcat2` err " does not fit the layout of type " `vcat2` indent' (ansiP t2)
  ansiP (TypeWarningAsError w)       = ansiP w

instance PrettyAnsi TypeWarning where
  ansiP (UnusedLocalBind v) = warn "[--Wunused-local-binds]" `vcat2` indent' (warn "Defined but not used:" <+> ansiP v)
  ansiP (TakeTakenField f t) = warn "[--Wdodgy-take-put]" `vcat2` indent' (warn "Take a taken field" <+> fieldname f
                                  <+> warn "from type" `vsep2` ansiP t)
  ansiP (PutUntakenField f t) = warn "[--Wdodgy-take-put]" `vcat2` indent' (warn "Put an untaken field" <+> fieldname f
                                  <+> warn "into type" `vsep2` ansiP t)

instance PrettyAnsi TcLog where
  ansiP = either ((err "Error:" <+>) . ansiP) ((warn "Warning:" <+>) . ansiP)

instance PrettyAnsi VarOrigin where
  ansiP (ExpressionAt l) = warn ("the term at location " ++ show l)
  ansiP (TermInType e t l) = warn "the term" <+> ansiP e `vsep2`
                              warn "of type" <+> ansiP t `vsep2`
                              warn ("at location" ++ show l)
  ansiP (TypeOfExpr e bs l) = warn "the type of expression" <+> ansiP e <> bangs bs `vsep2`
                               warn ("at location " ++ show l)
    where bangs [] = empty; bangs ts = empty <+> symbol "!" <> parens (spaceList $ fmap letbangvar bs)
  ansiP (TypeOfPatn p l) = warn "the type of pattern" <+> ansiP p `vsep2`
                            warn ("at location " ++ show l)
  ansiP (TypeOfIrrefPatn p l) = warn "the type of pattern" <+> ansiP p `vsep2`
                                 warn ("at location " ++ show l)
  ansiP (ImplicitTypeApp l) = warn ("implicit type application at location " ++ show l) 
  ansiP (ImplicitLayoutApp l) = warn ("implicit layout application at location " ++ show l) 
  ansiP (TypeHole l) = warn ("type hole at location " ++ show l)
  ansiP (LayoutHole l) = warn ("layout hole at location " ++ show l)
  ansiP (UnifyingRows r1 r2) = warn "the solver when trying to unify rows" `vsep2`
                                ansiP r1 <+> warn "and" <+> ansiP r2
  ansiP (SinkFloat u s t) = warn "the solver's sink/float phase when breaking up type" <+> ansiP u `vsep2`
                             warn "to" <+> ansiP s `vsep2`
                             warn "because it should have the same structure as type" <+> ansiP t
  ansiP (SinkFloatRow u r t1 t2) = warn ("the solver's sink/float phase when breaking up row variable ?" ++ show u) `vsep2`
                                    warn "to" <+> ansiP r `vsep2`
                                    warn "when comparing types" <+> ansiP t1 <+> warn "and" <+> ansiP t2
  ansiP (SinkFloatEntry e t1 t2) = warn "populating the entry" <+> ansiP e `vsep2`
                                    warn "when comparing types" <+> ansiP t1 <+> warn "and" <+> ansiP t2 `vsep2`
                                    warn "in the solver's sink/float phase"
  ansiP (SinkFloatSigil t1 t2) = warn "the sigil in" <+> ansiP t1 `vsep2`
                                  warn "when comparing it with" <+> ansiP t2 `vsep2`
                                  warn "in the solver's sink/float phase"
  ansiP (BoundOf a b d) = warn ("taking the " ++ show d ++ " of") `vsep2`
                           ansiP a <+> warn "and" <+> ansiP b
  ansiP (EqualIn e1 e2 t1 t2) = __todo "ansiP (VarOrigin)"
  ansiP (BlockedByType t l) = warn "other errors in type well-formedness of" <+> ansiP t
                           `vsep2` warn ("at location " ++ show l)
  ansiP (BlockedByLayout r l) = warn "other errors in layout well-formedness of" <+> ansiP r
                             `vsep2` warn ("at location " ++ show l)
  ansiP (OtherOrigin s) = warn s

analyseLeftover :: Constraint -> I.IntMap VarOrigin -> Doc AnsiStyle
{-
analyseLeftover c@(F t :< F u) os
    | Just t' <- flexOf t
    , Just u' <- flexOf u
    = vcat $ err "A subtyping constraint" <+>  ansiP c <+> err "can't be solved because both sides are unknown."
           : map (\i -> warn "• The unknown" <+> ansiP (U i) <+> warn "originates from" <+> ansiP (I.lookup i os))
                 (nub [t',u'])
    | Just t' <- flexOf t
    = vcat $ (case t of
        U _ -> err "Constraint" <+> ansiP c <+> err "can't be solved as another constraint blocks it."
        _   -> err "A subtyping constraint" <+>  ansiP c
           <+> err "can't be solved because the LHS is unknown and uses non-injective operators (like !).")
             : map (\i -> warn "• The unknown" <+> ansiP (U i) <+> warn "originates from" <+> ansiP (I.lookup i os)) ([t'])
    | Just u' <- flexOf u
    = vcat $ (case u of
        U _ -> err "Constraint" <+> ansiP c <+> err "can't be solved as another constraint blocks it."
        _   -> err "A subtyping constraint" <+>  ansiP c
           <+> err "can't be solved because the RHS is unknown and uses non-injective operators (like !).")
             : map (\i -> warn "• The unknown" <+> ansiP (U i) <+> warn "originates from" <+> ansiP (I.lookup i os)) ([u']) -}
analyseLeftover c os =
#ifdef BUILTIN_ARRAYS
  case bifoldMap (\t -> unifVars t ++ unknowns t) unifLVars c of
#else
  case bifoldMap unifVars unifLVars c of
#endif
    [] -> err "Constraint" `vsep2` indent' (ansiP c) `vsep2` err "cannot be solved, or is unsatisfiable."
    xs -> err "Constraint" `vsep2` indent' (ansiP c) `vsep2` err "cannot be solved, or is unsatisfiable."
          `vcat2` indent' (context "with relevant unifiers:"
               `vcat2` indent' (vcat $ fmap (originInfo os) xs))
  where originInfo os x = warn "•" <+>
                            align (warn "The unknown" <+> ansiP (U x) <+> warn "originates from" <+>
                            prettyOrigin (I.lookup x os))
        prettyOrigin Nothing  = warn "unknown origin"
        prettyOrigin (Just o) = ansiP o

instance PrettyAnsi Constraint where
  ansiP (a :< b)         = ansiP a `fillSep2` warn ":<" `fillSep2` ansiP b
  ansiP (a :=: b)        = ansiP a `fillSep2` warn ":=:" `fillSep2` ansiP b
  ansiP (a :& b)         = prettyPrec 4 a `fillSep2` warn ":&" `fillSep2` prettyPrec 3 b
  ansiP (Upcastable a b) = ansiP a `fillSep2` warn "~>" `fillSep2` ansiP b
  ansiP (Share  t m)     = warn "Share" <+> ansiP t
  ansiP (Drop   t m)     = warn "Drop" <+> ansiP t
  ansiP (Escape t m)     = warn "Escape" <+> ansiP t
  ansiP (Unsat e)        = err  "Unsat"
  ansiP (SemiSat w)      = warn "SemiSat"
  ansiP (Sat)            = warn "Sat"
  ansiP (UnboxedNotRecursive t)
                          = warn "UnboxedNotRecursive" <+> ansiP t
  ansiP (NotReadOnly s)  = warn "NotReadOnly" <+> prettyS s
    where prettyS (Left  l) = ansiP l
          prettyS (Right x) = warn ('?':show x)
  ansiP (Exhaustive t p) = warn "Exhaustive" <+> ansiP t <+> ansiP p
  ansiP (Solved t)       = warn "Solved" <+> ansiP t
  ansiP (IsPrimType t)   = warn "IsPrimType" <+> ansiP t
  ansiP (x :@ _)         = ansiP x
#ifdef BUILTIN_ARRAYS
  ansiP (Arith e)        = ansiP e
  ansiP (e1 :==: e2)     = ansiP e1 `fillSep2` warn ":==:" `fillSep2` ansiP e2
  ansiP (a :-> b)        = prettyPrec 2 a `fillSep2` warn ":->" `fillSep2` prettyPrec 1 b
#endif
  ansiP (LayoutOk t)     = warn "LayoutOk" <+> ansiP t
  ansiP (l :~ n)         = ansiP l `fillSep2` warn ":~" `fillSep2` ansiP n
  ansiP (l :~< m)        = ansiP l `fillSep2` warn ":~<" `fillSep2` ansiP m
  ansiP (a :~~ b)        = ansiP a `fillSep2` warn ":~~" `fillSep2` ansiP b

-- a more verbose version of constraint pretty-printer which is mostly used for debugging
prettyC :: Constraint -> Doc AnsiStyle
prettyC (Unsat e) = errbd "Unsat" `vsep2` ansiP e
prettyC (SemiSat w) = warn "SemiSat" -- `vsep2` ansiP w
prettyC (a :& b) = prettyCPrec 4 a `fillSep2` warn ":&" `vsep2` prettyCPrec 3 b
prettyC (c :@ e) = prettyCPrec 3 c & (if __cogent_ddump_tc_ctx then (`fillSep2` prettyCtx e False) else (`fillSep2` warn ":@ ..."))
#ifdef BUILTIN_ARRAYS
prettyC (a :-> b) = prettyCPrec 2 a `fillSep2` warn ":->" `fillSep2` prettyCPrec 1 b
#endif
prettyC c = ansiP c

prettyCPrec :: Int -> Constraint -> Doc AnsiStyle
prettyCPrec l x | prec x < l = prettyC x
                | otherwise  = parens (indent (prettyC x))

instance PrettyAnsi SourceObject where
  ansiP (TypeName n) = typename n
  ansiP (ValName  n) = varname n
  ansiP (RepName  n) = reprname n
  ansiP (DocBlock' _) = __fixme empty  -- FIXME: not implemented

instance PrettyAnsi ReorganizeError where
  ansiP CyclicDependency = err "cyclic dependency"
  ansiP DuplicateTypeDefinition = err "duplicate type definition"
  ansiP DuplicateValueDefinition = err "duplicate value definition"
  ansiP DuplicateRepDefinition = err "duplicate repr definition"
  ansiP NonStrictlyPositive = err "non strictly positive occurence of recursive type"
  ansiP RecParShadowsTyVar = err "recursive parameter shadows type variable"

instance PrettyAnsi Subst where
  ansiP (Subst m) = ansiP m

instance PrettyAnsi AssignResult where
  ansiP (Type t) = ansiP t
  ansiP (Sigil s) = ansiP s
  ansiP (Row (Left r)) = ansiP r
  ansiP (Row (Right sh)) = ansiP sh
  ansiP (Layout' l) = ansiP l
#ifdef BUILTIN_ARRAYS
  ansiP (ARow r) = ansiP r
  ansiP (Expr e) = ansiP e
  ansiP (Hole h) = case h of
                      Nothing -> empty
                      Just h' -> keyword "@take" <+> parens (ansiP h')
#endif
  ansiP (RecP r) = ansiP r

instance PrettyAnsi RP where
  ansiP (Mu t) = typevar t
  ansiP (None) = ansiP "None"
  ansiP (UP i) = warn ('?':show i)

instance PrettyAnsi r => PrettyAnsi (Sigil r) where
  ansiP (Boxed False l) = keyword "[W]" <+> parens (ansiP l)
  ansiP (Boxed True  l) = keyword "[R]" <+> parens (ansiP l)
  ansiP Unboxed  = keyword "[U]"

instance (PrettyAnsi t) => PrettyAnsi (Row.Row t) where
  ansiP r =
    let rowFieldsDoc =
          hsep $ punctuate (text ",") $ map ansiP (Row.entries r)
        prettyRowVar Nothing  = symbol "✗"
        prettyRowVar (Just x) = symbol "?" <> ansiP x
     in enclose (text "❲") (text "❳") (rowFieldsDoc <+> symbol "|" <+> prettyRowVar (Row.var r))

instance PrettyAnsi t => PrettyAnsi (Row.Entry t) where
  ansiP e =
    let tkDoc = case Row.taken e of
          True  -> text "taken"
          False -> text "present"
    in text (Row.fname e) <+> text ":" <+> ansiP (Row.payload e) <+>
       parens tkDoc

instance (PrettyAnsi e, Show e) => PrettyAnsi (ARow.ARow e) where
  ansiP (ARow.ARow m u a v) = typesymbol "A-row" <+> brackets (ansiP m <+> symbol "|" <+> ansiP u <> all <> var)
    where var = case v of Nothing -> empty; Just x -> (symbol " |" <+> symbol "?" <> ansiP x)
          all = case a of Nothing -> empty
                          Just True  -> (symbol " |" <+> text "all taken")
                          Just False -> (symbol " |" <+> text "all put"  )

instance PrettyAnsi a => PrettyAnsi (I.IntMap a) where
  ansiP = align . vcat . map (\(k,v) -> ansiP k <+> text "|->" <+> ansiP v) . I.toList


instance PrettyAnsi DataLayoutTcError where
  ansiP (OverlappingBlocks blks)
    = err "The following pairs of declared data blocks cannot overlap:" `vcat2`
      vcat (map (\((r1,c1),(r2,c2)) -> indent' (ansiP r1 <+> ansiP c1 `vsep2`
                                                err "and" `vsep2`
                                                ansiP r2 <+> ansiP c2))
           (fmap unOverlappingAllocationBlocks blks))
  ansiP (UnknownDataLayout r ctx) 
    =  err "Undeclared data layout" <+> reprname r `vcat2` ansiP ctx

  ansiP (BadDataLayout l p) = err "Bad data layout" <+> ansiP l
  ansiP (TagSizeTooLarge ctx) =
    err "Variant tag allocated more bits than necessary" `vcat2` ansiP ctx
  ansiP (TagNotSingleBlock ctx) =
    err "Variant tag must be a single block of bits" `vcat2` ansiP ctx
  ansiP (SameTagValues context name1 name2 value) =
    err "Alternatives" <+> tagname name1 <+> err "and" <+> tagname name2 <+> err "of same variant cannot have the same tag value" <+> literal (ansiP value) `vcat2`
    indent (ansiP context)
  ansiP (OversizedTagValue context range altName value) =
    err "Oversized tag value" <+> literal (ansiP value) <+> err "for tag data block" <+> ansiP range <+> err "in variant alternative" <+> tagname altName `vcat2`
    indent (ansiP context)
  ansiP (TagLargerThanInt context) =
    err "The size of the tag is larger than 32 bits" `vcat2`
    indent (ansiP context)
  ansiP (ZeroSizedBitRange context) =
    err "Zero-sized bit range" `vcat2`
    indent (ansiP context)
  ansiP (UnknownDataLayoutVar n ctx) =
    err "Undeclared data layout variable" <+> dlvarname n `vcat2` indent (ansiP ctx)
  ansiP (DataLayoutArgsNotMatch n exp act ctx) =
    err "Number of arguments for data layout synonym" <+> reprname n <+> err "not matched,"
    `fillSep2` err "expected" <+> int exp <+> err "args, but actual" <+> int act <+> err "args"
    `vcat2` indent (ansiP ctx)
  ansiP (OverlappingFields fs ctx) =
    err "Overlapping fields" <+> foldr1 (<+>) (fmap fieldname fs) `vcat2` indent (ansiP ctx)
  ansiP (CyclicFieldDepedency fs ctx) =
    err "Cyclic dependency of fields" <+> foldr1 (<+>) (fmap fieldname fs) `vcat2` indent (ansiP ctx)
  ansiP (NonExistingField f ctx) =
    err "Non-existing field" <+> symbol "after" <+> fieldname f `vcat2` indent (ansiP ctx)
  ansiP (InvalidUseOfAfter f ctx) =
    err "The use of" <+> symbol "after" <+> fieldname f <+> err "layout expression is invalid" `vcat2` indent (ansiP ctx)
  ansiP (AfterUnknownOffset f ctx) =
    err "Cannot use (possibly implicit)" <+> symbol "after" <+> fieldname f <+> err "when its offset is unknown"
  ansiP (InvalidEndianness end ctx) =
    err "Endianness" <+> ansiP end <+> err "can only be applied to int sizes"
  ansiP (ArrayElementNotByteAligned sz p) = err "array element has a layout of size" <+> ansiP sz `vcat2`
                                             err "whereas it should be aligned to bytes"

instance PrettyAnsi DataLayoutPath where
  ansiP (InField n po ctx) = context' "for field" <+> fieldname n <+> context' "(" <> ansiP po <> context' ")" `fillSep2` ansiP ctx
  ansiP (InTag ctx)        = context' "for the variant tag block" `fillSep2` ansiP ctx
  ansiP (InAlt t po ctx)   = context' "for the constructor" <+> tagname t <+> context' "(" <> ansiP po <> context' ")" `fillSep2` ansiP ctx
#ifdef BUILTIN_ARRAYS
  ansiP (InElmt po ctx)    = context' "in the array element (" <> ansiP po <> context' ")" `fillSep2` ansiP ctx
#endif
  ansiP (InDecl n p)       = context' "in the representation" <+> reprname n <+> context' "(" <> ansiP p <> context' ")"
  ansiP (PathEnd)          = mempty

instance PrettyAnsi a => PrettyAnsi (DataLayout a) where
  ansiP (Layout l) = symbol "layout" <+> ansiP l
  ansiP CLayout = symbol "c-layout"

instance PrettyAnsi a => PrettyAnsi (DataLayout' a) where
  ansiP UnitLayout =
    parens (literal (symbol "unit"))

  ansiP PrimLayout {bitsDL, endianness} =
    parens (ansiP bitsDL <+> keyword "using" <+> ansiP endianness)

  ansiP SumLayout {tagDL, alternativesDL} =
    parens (ansiP tagDL) <> variant (map prettyAlt $ M.toList alternativesDL)
    where prettyAlt (n,(v,l)) = tagname n <> parens (integer $ fromIntegral v) <> colon <> ansiP l

  ansiP RecordLayout {fieldsDL} =
    record (map prettyField $ M.toList fieldsDL)
    where prettyField (f,l) = fieldname f <+> symbol ":" <+> ansiP l
#ifdef BUILTIN_ARRAYS
  ansiP (ArrayLayout d l) = parens (ansiP d) <> brackets (ansiP l)
#endif
  ansiP (VarLayout n s) = (dullcyan . string . ("_l" ++) . show $ natToInt n) <> prettyOffset s
    where prettyOffset 0 = empty
          prettyOffset n = space <> symbol "offset" <+> integer n <> symbol "b"

instance PrettyAnsi (Allocation' p) where
  ansiP (Allocation bs vs) = list (map ansiP bs) <> prettyAllocVars vs
    where prettyAllocVars [] = empty
          prettyAllocVars vs = empty <+> symbol "#" <> list (map go vs)
            where go (v,s) = varname v <> brackets (integer s <> symbol "b")

instance PrettyAnsi a => PrettyAnsi (S.Set a) where
  ansiP s = list $ S.foldr ((:) . ansiP) [] s

instance {-# OVERLAPPING #-} PrettyAnsi (AllocationBlock p) where
  ansiP (br, _) = ansiP br

instance PrettyAnsi BitRange where
  ansiP br = literal (ansiP $ bitSizeBR br) <> symbol "b" <+> symbol "at" <+> literal (ansiP $ bitOffsetBR br) <> symbol "b"


-- helper functions
-- ~~~~~~~~~~~~~~~~~~~~~~~~~

-- assumes positive `n`
nth :: Int -> Doc AnsiStyle
nth n = context $ show n ++ ordinalOf n

ordinalOf :: Int -> String
ordinalOf n =
  let (d,m) = divMod n 10
   in if d == 1
      then "th"
      else
        case m of
          1 -> "st"
          2 -> "nd"
          3 -> "rd"
          _ -> "th"


-- ctx -> indent -> doc
prettyCtx :: ErrorContext -> Bool -> Doc AnsiStyle
prettyCtx (SolvingConstraint c) _ = context "from constraint" <+> indent (ansiP c)
prettyCtx (ThenBranch) _ = context "in the" <+> keyword "then" <+> context "branch"
prettyCtx (ElseBranch) _ = context "in the" <+> keyword "else" <+> context "branch"
prettyCtx (NthBranch n) _ = context "in the" <+> nth n <+> context "branch of a multiway-if"
prettyCtx (InExpression e t) True = context "when checking that the expression at ("
                                      <> ansiP (posOfE e) <> context ")"
                                      `vsep2` (indent' (ansiP (stripLocE e)))
                                      `vsep2` context "has type" `vsep2` (indent' (ansiP t))
prettyCtx (InExpression e t) False = context "when checking the expression at ("
                                       <> ansiP (posOfE e) <> context ")"
prettyCtx (InType l t) True  = context "when checking well-formedness of the type at ("
                                 <> ansiP l <> context ")"
                                 `vsep2` indent' (ansiP t)
prettyCtx (InType l t) False = context "when checking well-formedness of the type at ("
                                 <> ansiP l <> context ")"
-- FIXME: more specific info for patterns
prettyCtx (InPattern p) True = context "when checking the pattern at ("
                                 <> ansiP (posOfP p) <> context ")"
                                 `vsep2` (indent' (ansiP (stripLocP p)))
prettyCtx (InPattern p) False = context "when checking the pattern at ("
                                  <> ansiP (posOfP p) <> context ")"
prettyCtx (InIrrefutablePattern ip) True = context "when checking the pattern at ("
                                             <> ansiP (posOfIP ip) <> context ")"
                                             `vsep2` (indent' (ansiP (stripLocIP ip)))
prettyCtx (InIrrefutablePattern ip) False = context "when checking the pattern at ("
                                              <> ansiP (posOfIP ip) <> context ")"
prettyCtx (NthAlternative n p) _ = context "in the" <+> nth n <+> context "alternative" <+> ansiP p
prettyCtx (InDefinition p tl) _ = context "in the definition at (" <> ansiP p <> context ")"
                               `vsep2` context "for the" <+> helper tl
  where helper (TypeDec n _ _) = context "type synonym" <+> typename n
        helper (AbsTypeDec n _ _) = context "abstract type" <+> typename n
        helper (AbsDec n _) = context "abstract function" <+> varname n
        helper (ConstDef v _ _) = context "constant" <+> varname v
        helper (FunDef v _ _) = context "function" <+> varname v
        helper (RepDef (DataLayoutDecl _ n v _)) = context "representation" <+> reprname n <+> hsep (fmap varname v)
        helper _  = __impossible "helper"
prettyCtx (AntiquotedType t) i = (if i then (`vsep2` indent' (ansiP (stripLocT t))) else id)
                               (context "in the antiquoted type at (" <> ansiP (posOfT t) <> context ")" )
prettyCtx (AntiquotedExpr e) i = (if i then (`vsep2` indent' (ansiP (stripLocE e))) else id)
                               (context "in the antiquoted expression at (" <> ansiP (posOfE e) <> context ")" )
prettyCtx (InAntiquotedCDefn n) _ = context "in the antiquoted C definition" <+> varname n
prettyCtx (CustomisedCodeGen t) _ = context "in customising code-generation for type" <+> ansiP t

handleTakeAssign :: (PatnType ip, PrettyAnsi ip) => Maybe (FieldName, ip) -> Doc AnsiStyle
handleTakeAssign Nothing = fieldname ".."
handleTakeAssign (Just (s, e)) | isPVar e s = fieldname s
handleTakeAssign (Just (s, e)) = fieldname s <+> symbol "=" <+> ansiP e

handlePutAssign :: (ExprType e, PrettyAnsi e) => Maybe (FieldName, e) -> Doc AnsiStyle
handlePutAssign Nothing = fieldname ".."
handlePutAssign (Just (s, e)) | isVar e s = fieldname s
handlePutAssign (Just (s, e)) = fieldname s <+> symbol "=" <+> ansiP e


-- top-level function
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~

-- typechecker errors/warnings
prettyTWE :: Int -> ContextualisedTcLog -> Doc AnsiStyle
prettyTWE th (ectx, l) = ansiP l `vsep2` indent' (vcat (map (flip prettyCtx True ) (take th ectx)
                                                  ++ map (flip prettyCtx False) (drop th ectx)))

-- reorganiser errors
prettyRE :: (ReorganizeError, [(SourceObject, SourcePos)]) -> Doc AnsiStyle
prettyRE (msg,ps) = ansiP msg `vsep2`
                    indent' (vcat (map (\(so,p) -> context "-" <+> ansiP so
                                               <+> context "(" <> ansiP p <> context ")") ps))

prettyPrint :: PrettyAnsi a => (Doc AnsiStyle -> Doc AnsiStyle) -> [a] -> SimpleDocStream AnsiStyle
prettyPrint f = renderSmart 1.0 120 . f . vcat . map ansiP

prettyPrintError :: (Doc AnsiStyle -> Doc AnsiStyle) -> [Doc AnsiStyle] -> SimpleDocStream AnsiStyle
prettyPrintError f = renderSmart 1.0 120 . f . vcat

