--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

module Isabelle.PrettyHelper where

--import Text.PrettyPrint.ANSI.Leijen
import Prettyprinter
import Text.Parsec.Prim
import Text.Parsec.Expr 

import Control.Monad.Identity

import Isabelle.PrettyAnsi

type Precedence = Int

prettyParen :: Bool -> Doc ann -> Doc ann
prettyParen b d = if b then parens d else d

data BinOpRec = BinOpRec { binOpRecAssoc :: Assoc, binOpRecPrec :: Precedence,
                           binOpRecSym :: String }

data UnOpRec = UnOpRec { unOpRecPrec :: Precedence, unOpRecSym :: String }

prettyBinOp :: Precedence -> (Precedence -> a -> Doc ann) -> BinOpRec -> (Precedence -> b -> Doc ann) -> a -> b -> Doc ann
prettyBinOp p prettyLeft b prettyRight left right = 
  prettyParen (p > p') $ prettyLeft lp left <+> string (binOpRecSym b) <+> prettyRight rp right
    where
      p' = binOpRecPrec b
      (lp,rp) = case binOpRecAssoc b of
                  AssocLeft -> (p',p'+1)
                  AssocRight -> (p'+1, p')

-- FIXME: zilinc: could be buggy
prettyUnOp :: Precedence -> UnOpRec -> (Precedence -> a -> Doc ann) -> a -> Doc ann
prettyUnOp p u prettyTerm term = prettyParen (p > p') $ string (unOpRecSym u) <> prettyTerm p' term
  where p' = unOpRecPrec u

