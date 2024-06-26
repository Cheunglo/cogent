--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

{-# LANGUAGE DeriveDataTypeable, FlexibleContexts #-}

module Isabelle.OuterAST where

import Data.Data
import Data.List
-- import Data.Typeable
import Text.Parsec.Expr (Assoc(..))
--import Text.PrettyPrint.ANSI.Leijen
import Prettyprinter
#if __GLASGOW_HASKELL__ >= 709
import Prelude hiding ((<$>))
#endif

import Isabelle.PrettyAnsi
import Isabelle.InnerAST (Arity, prettyTypeVars, Type(TyVar), PrettyPlus, prettyPlus)
import Isabelle.PrettyHelper (BinOpRec(..), prettyBinOp)

--
-- A note on the design of this AST
--
-- Although the ISAR Reference Manual was consulted while writing this AST we do not follow it to
-- the letter. Because we are only implementing a subset of the functionality it is sometimes more
-- elegant to re-order the structure of the AST in such a way that the dependencies between
-- components is quite different to the structure of the grammar in the reference manual.
--

type Name = String

--
-- The type parameters @types@ and @terms@ exist so that one can plug in a parser for the type
-- language and one for the term language, respectively.
--
data Theory types terms = Theory { thyName :: String, thyImports :: TheoryImports, thyBody :: [TheoryDecl types terms] } 
                        deriving (Data, Typeable, Show)

newtype TheoryImports = TheoryImports [TheoryImport] deriving (Data, Typeable, Show)

type TheoryImport = String

data TheoryDecl types terms = Definition    (Def types terms)
                            | OverloadedDef (Def types terms) (Sig types) -- def for specific fun name, and overloaded fun sig
                            | Abbreviation (Abbrev types terms)
                            | ContextDecl  (Context types terms)
                            | LemmaDecl    (Lemma types terms)
                            | LemmasDecl   (Lemmas types terms)
                            | TypeSynonym  (TypeSyn types terms)
                            | TypeDeclDecl (TypeDecl types terms)
                            | ConstsDecl   (Consts types terms)
                            | RecordDecl   (Record types terms) 
                            | DataTypeDecl (Datatype types terms)
                            | ClassDecl    (Class types terms)
                            | InstantiationDecl (Instantiation types terms)
                            | InstanceDecl (Instance types terms)
                            | FunFunction  Bool (FunFunc types terms)  -- True is fun / False is function
                            | TheoryString String
                            deriving (Data, Typeable, Show)

data Def types terms = Def { defSig :: Maybe (Sig types), defTerm :: terms} deriving (Data, Typeable, Show)

data Sig types = Sig { sigName :: String, sigType :: Maybe types } deriving (Data, Typeable, Show)

data Abbrev types terms = Abbrev { abbrevSig :: Maybe (Sig types), abbrevTerm :: terms } deriving (Data, Typeable, Show)

data Lemma types terms = Lemma { lemmaSchematic :: Bool
                               , lemmaThmDecl :: Maybe TheoremDecl
                               , lemmaProps :: [terms]
                               , lemmaProof :: Proof } deriving (Data, Typeable, Show)

-- not all TheoryDecls are legal in Contexts, but most
data Context types terms = Context { cName :: String
                                   , cBody :: [TheoryDecl types terms]
                                   } deriving (Data, Typeable, Show)

data Lemmas types terms = Lemmas { lemmasName :: TheoremDecl
                                 , lemmasThms :: [TheoremDecl] } deriving (Data, Typeable, Show)

data TypeSyn types terms = TypeSyn { typeName :: Name
                                   , synonym :: types
                                   , tsTypeVars :: [String]
                                   } deriving (Data, Typeable, Show)

data TypeDecl types terms = TypeDecl { tdeclName :: Name
                                     , tdeclTypeVars :: [String]
                                     } deriving (Data, Typeable, Show)

data Consts types terms = Consts { constsSig :: Sig types } deriving (Data, Typeable, Show)

data RecField types terms = RecField { fieldName :: Name
                                     , fieldType :: types
                                     } deriving (Data, Typeable, Show)

data Record types terms = Record { recName :: Name
                                 , recFields :: [RecField types terms]
                                 , recTypeVars :: [String]
                                 } deriving (Data, Typeable, Show)

data DTCons types terms = DTCons { conName :: Name
                                 , conTypes :: [types]
                                 } deriving (Data, Typeable, Show)

data Datatype types terms = Datatype { dtName :: Name
                                     , dtCons :: [DTCons types terms]
                                     , dtTypeVars :: [String]
                                     } deriving (Data, Typeable, Show)

data Class types terms = Class { clSpec :: ClassSpec types terms
                               , clBody :: [TheoryDecl types terms] 
                               } deriving (Data, Typeable, Show)

data ClassSpec types terms = ClassSpec deriving (Data, Typeable, Show)  -- TODO: zilinc

data Instantiation types terms = Instantiation { instnNames :: [Name]
                                               , instnArity :: Arity 
                                               , instnBody  :: [TheoryDecl types terms]
                                               } deriving (Data, Typeable, Show)

data Instance types terms = Instance { instHead :: InstanceHead
                                     , instBody :: [TheoryDecl types terms] }
                          deriving (Data, Typeable, Show)

data InstanceHead = InstanceHeadNo
                  | InstanceHeadTh { ihThNames :: [Name]
                                   , ihThArity :: Arity 
                                   } 
                  | InstanceHeadIn { ihInName  :: Name
                                   , ihInRel   :: ClassRel
                                   , ihInSuper :: Name
                                   }
                  deriving (Data, Typeable, Show)

data ClassRel = ClassLessThan | ClassSubsetOf deriving (Data, Typeable, Show)

data FunFunc types terms = FunFunc { funSig :: [Sig types]
                                   , funDef :: Equations types terms
                                   } deriving (Data, Typeable, Show)

data Equations types terms = Equations [terms] deriving (Data, Typeable, Show)

data TheoremDecl = TheoremDecl { thmName :: Maybe Name, thmAttributes :: [Attribute] }
  deriving (Data, Typeable, Show)

data Attribute = Attribute Name [Name] deriving (Data, Typeable, Show)

data Proof = Proof [Method] ProofEnd deriving (Data, Typeable, Show)

data ProofEnd = ProofDone
              | ProofSorry deriving (Data, Typeable, Show)

data Method = Method Name [Name]
            | MethodModified Method MethodModifier
            | MethodCompound MethodBinOp Method Method -- compound methods
            deriving (Data, Typeable, Show)
  
data MethodModifier = MMOptional
                    | MMOneOrMore
                    | MMGoalRestriction (Maybe Int) deriving (Data, Typeable, Show)

data MethodBinOp =
    MethodSeq  -- wp, simp
  | MethodOr   -- wp | simp 
  deriving (Data, Typeable, Show)

--
-- MethodSeq (comma) binds more tightly than MethodOr (vertical bar)
--
methodBinOpRec :: MethodBinOp -> BinOpRec
methodBinOpRec b = case b of
  MethodSeq -> BinOpRec AssocRight 3 "," 
  MethodOr  -> BinOpRec AssocRight 2 "|"

--
-- Pretty printing
--
vsepPad :: [Doc ann] -> Doc ann
vsepPad xs = empty `vcat2` vsep (intersperse empty xs) `vcat2` empty

quote :: Doc ann -> Doc ann
quote doc = char '"' <>  doc <> char '"'

prettyTheoryBase :: (Pretty terms, Pretty types) => Theory types terms -> Doc ann
prettyTheoryBase thy = (string "theory" <+> string (thyName thy)) `vcat2`
                     pretty (thyImports thy) `vcat2`
                     string "begin" `vcat2`
                     prettyThyDecls (thyBody thy) <>
                     string "end" `vcat2` empty

instance (Pretty terms, Pretty types) =>  Pretty (Theory types terms) where
  pretty = prettyTheoryBase

instance (Pretty terms, Pretty types) =>  PrettyAnsi (Theory types terms) where
  ansiP = prettyTheoryBase 

prettyThyDecls :: (Pretty terms, Pretty types) => [TheoryDecl types terms] -> Doc ann
prettyThyDecls [] = empty
prettyThyDecls thyDecls = (vsepPad . map pretty $ thyDecls) `vcat2` empty

prettyTheoryDeclBase :: (Pretty terms, Pretty types) => TheoryDecl types terms -> Doc ann
prettyTheoryDeclBase d = case d of
    Definition def      -> pretty def
    OverloadedDef def sig -> prettyOv def sig
    Abbreviation abbrev -> pretty abbrev
    ContextDecl c       -> pretty c
    LemmaDecl d'        -> pretty d'
    LemmasDecl ld       -> pretty ld
    TypeSynonym ts      -> pretty ts
    TypeDeclDecl td     -> pretty td
    ConstsDecl c        -> pretty c
    RecordDecl fs       -> pretty fs
    DataTypeDecl dt     -> pretty dt
    FunFunction ff f    -> (if ff then string "fun" else string "function") <+> pretty f
    TheoryString s      -> string s


instance (Pretty terms, Pretty types) => Pretty (TheoryDecl types terms) where
  pretty = prettyTheoryDeclBase

instance (Pretty terms, Pretty types) => PrettyAnsi (TheoryDecl types terms) where
  ansiP = prettyTheoryDeclBase

prettyContextBase :: (Pretty terms, Pretty types) => Context types terms -> Doc ann
prettyContextBase (Context name cDecls) = string "context" <+> string name <+> string "begin" `vcat2` 
                                          prettyThyDecls cDecls <> string "end"

instance (Pretty terms, Pretty types) => Pretty (Context types terms) where
  pretty = prettyContextBase

instance (Pretty terms, Pretty types) => PrettyAnsi (Context types terms) where
  ansiP = prettyContextBase

prettyLemmaBase :: (Pretty terms, Pretty types) => Lemma types terms -> Doc ann
prettyLemmaBase (Lemma schematic thmDecl props proof) = string (if schematic then "schematic_lemma" else "lemma") <+>
    pretty thmDecl <+> string ":" `vcat2` indent 2 (vsep (map (quote . pretty) props)) `vcat2` indent 2 (pretty proof)

instance (Pretty terms, Pretty types) => Pretty (Lemma types terms) where
  pretty = prettyLemmaBase

instance (Pretty terms, Pretty types) => PrettyAnsi (Lemma types terms) where
  ansiP = prettyLemmaBase

prettyLemmasBase :: (Pretty terms, Pretty types) => Lemmas types terms -> Doc ann
prettyLemmasBase (Lemmas name lems) = string "lemmas" <+>
    pretty name <+> string "=" `vcat2` indent 2 (vsep $ map pretty lems)

instance (Pretty terms, Pretty types) => Pretty (Lemmas types terms) where
  pretty = prettyLemmasBase

instance (Pretty terms, Pretty types) => PrettyAnsi (Lemmas types terms) where
  ansiP = prettyLemmasBase

prettyTypeSynBase :: (Pretty terms, Pretty types) => TypeSyn types terms -> Doc ann
prettyTypeSynBase (TypeSyn mbName typs tvs) = string "type_synonym" <+>
    prettyTypeVars (map TyVar tvs) <+>
    pretty mbName <+> string "=" <+> (quote . pretty) typs

instance (Pretty terms, Pretty types) => Pretty (TypeSyn types terms) where
  pretty = prettyTypeSynBase

instance (Pretty terms, Pretty types) => PrettyAnsi (TypeSyn types terms) where
  ansiP = prettyTypeSynBase

prettyTypeDeclBase :: (Pretty terms, Pretty types) => TypeDecl types terms -> Doc ann
prettyTypeDeclBase (TypeDecl tdName tvs) = string "typedecl" <+>
    prettyTypeVars (map TyVar tvs) <+> pretty tdName

instance (Pretty terms, Pretty types) => Pretty (TypeDecl types terms) where
  pretty = prettyTypeDeclBase

instance (Pretty terms, Pretty types) => PrettyAnsi (TypeDecl types terms) where
  ansiP = prettyTypeDeclBase

prettyConstsBase :: (Pretty terms, Pretty types) => Consts types terms -> Doc ann
prettyConstsBase (Consts sig) = string "consts" <+> pretty sig

instance (Pretty terms, Pretty types) => Pretty (Consts types terms) where
  pretty = prettyConstsBase

instance (Pretty terms, Pretty types) => PrettyAnsi (Consts types terms) where
  ansiP = prettyConstsBase

prettyRecordBase :: (Pretty terms, Pretty types) => Record types terms -> Doc ann
prettyRecordBase (Record rName rFields tvs) = string "record" <+>
  prettyTypeVars (map TyVar tvs) <+>
  pretty rName <+> string "=" `vcat2` 
  (vsep (map (\rf -> let RecField n t = rf in indent 2 (pretty n <+> string "::" <+> (quote . pretty) t)) rFields))

instance (Pretty terms, Pretty types) => Pretty (Record types terms) where
  pretty = prettyRecordBase

instance (Pretty terms, Pretty types) => PrettyAnsi (Record types terms) where
  ansiP = prettyRecordBase

prettyDTConsBase :: (Pretty terms, Pretty types) => DTCons types terms -> Doc ann
prettyDTConsBase (DTCons cn ts) = pretty cn <+> (hsep . map (quote . pretty) $ ts)

instance (Pretty terms, Pretty types) => Pretty (DTCons types terms) where
  pretty = prettyDTConsBase

instance (Pretty terms, Pretty types) => PrettyAnsi (DTCons types terms) where
  ansiP = prettyDTConsBase

prettyDatatypeBase :: (Pretty terms, Pretty types) => Datatype types terms -> Doc ann
prettyDatatypeBase (Datatype dtName dtCons tvs) = string "datatype" <+>
  prettyTypeVars (map TyVar tvs) <+>
  pretty dtName <+> string "=" `vcat2` (vsep $ punctuate (char '|') $ map (indent 2 . pretty) dtCons)

instance (Pretty terms, Pretty types) => Pretty (Datatype types terms) where
  pretty = prettyDatatypeBase

instance (Pretty terms, Pretty types) => PrettyAnsi (Datatype types terms) where
  ansiP = prettyDatatypeBase
 
prettyClassBase :: (Pretty terms, Pretty types) => Class types terms -> Doc ann
prettyClassBase (Class spec body) = string "class" <+> pretty spec
                             `vsep2` string "begin" 
                             `vsep2` prettyThyDecls body <> string "end" `vsep2` empty

instance (Pretty terms, Pretty types) => Pretty (Class types terms) where
  pretty = prettyClassBase

instance (Pretty terms, Pretty types) => PrettyAnsi (Class types terms) where
  ansiP = prettyClassBase

prettyClassSpecBase :: (Pretty terms, Pretty types) => ClassSpec types terms -> Doc ann
prettyClassSpecBase ClassSpec = error "TODO: instance Pretty (ClassSpec types terms)"  -- TODO: zilinc

instance (Pretty terms, Pretty types) => Pretty (ClassSpec types terms) where
  pretty = prettyClassSpecBase

instance (Pretty terms, Pretty types) => PrettyAnsi (ClassSpec types terms) where
  ansiP = prettyClassSpecBase

prettyInstantiationBase :: (Pretty terms, Pretty types) => Instantiation types terms -> Doc ann
prettyInstantiationBase (Instantiation names arity body) = 
  string "instantiation" <+> sep (punctuate (string "and") (map pretty names))
  <+> string "::" <+> pretty arity
  `vsep2` string "begin" 
  `vsep2` prettyThyDecls body <> string "end" `vsep2` empty

instance (Pretty terms, Pretty types) => Pretty (Instantiation types terms) where
  pretty = prettyInstantiationBase

instance (Pretty terms, Pretty types) => PrettyAnsi (Instantiation types terms) where
  ansiP = prettyInstantiationBase

prettyInstanceBase :: (Pretty terms, Pretty types) => Instance types terms -> Doc ann
prettyInstanceBase (Instance head body) = 
  string "instance" <+> pretty head
  `vsep2` prettyThyDecls body

instance (Pretty terms, Pretty types) => Pretty (Instance types terms) where
  pretty = prettyInstanceBase

instance (Pretty terms, Pretty types) => PrettyAnsi (Instance types terms) where
  ansiP = prettyInstanceBase

instance Pretty InstanceHead where
  pretty (InstanceHeadNo) = empty
  pretty (InstanceHeadTh names arity) = 
    sep (punctuate (string "and") (map pretty names)) <+> string "::" <+> pretty arity
  pretty (InstanceHeadIn name rel super) =
    pretty name <+> pretty rel <+> pretty super

instance PrettyAnsi InstanceHead where
  ansiP = pretty

instance Pretty ClassRel where
  pretty ClassLessThan = string "<"
  pretty ClassSubsetOf = string "⊆"  -- FIXME: zilinc

instance PrettyAnsi ClassRel where
  ansiP = pretty

prettyFunFuncBase :: (Pretty types, Pretty terms) => FunFunc types terms -> Doc ann
prettyFunFuncBase (FunFunc sig bd) = (encloseSep empty empty (string "and" <> space) (map pretty sig)) -- FIXME: `and' on a new line / zilinc
                            <+> string "where"
                            `vcat2` align (pretty bd)

instance (Pretty types, Pretty terms) => Pretty (FunFunc types terms) where
  pretty = prettyFunFuncBase

instance (Pretty types, Pretty terms) => PrettyAnsi (FunFunc types terms) where
  ansiP = prettyFunFuncBase

prettyEquationsBase :: (Pretty types, Pretty terms) => Equations types terms -> Doc ann
prettyEquationsBase (Equations terms) = vsep $ punctuate (space <> string "|") $ map (dquotes . pretty) terms

instance (Pretty types, Pretty terms) => Pretty (Equations types terms) where
  pretty = prettyEquationsBase

instance (Pretty types, Pretty terms) => PrettyAnsi (Equations types terms) where
  ansiP = prettyEquationsBase

instance Pretty TheoremDecl where
  pretty (TheoremDecl mbName attributes)
    | Nothing <- mbName, null attributes =
        error "In TheoremDecl, name == Nothing and attributes == [] is not allowed"
    | otherwise = maybe empty string mbName <> pattrs
       where pattrs = case attributes of
                  [] -> empty
                  attrs -> brackets . sep . punctuate comma $ map pretty attrs

instance PrettyAnsi TheoremDecl where
  ansiP = pretty

instance Pretty Attribute where
  pretty (Attribute n [])   = string n
  pretty (Attribute n args) = string n <+> (hsep . map string $ args)

instance PrettyAnsi Attribute where
  ansiP = pretty

instance Pretty Proof where
  pretty (Proof methods proofEnd) =
    (vsep . map (\m -> string "apply" <+> pretty m) $ methods) `vcat2` pretty proofEnd

instance PrettyAnsi Proof where
  ansiP = pretty

instance Pretty ProofEnd where
  pretty e = string $ case e of
    ProofDone  -> "done"
    ProofSorry -> "sorry"

instance PrettyAnsi ProofEnd where
  ansiP = pretty

instance Pretty Method where
  pretty = prettyMethodTopLevel 0

instance PrettyAnsi Method where
  ansiP = pretty

prettyMethodTopLevel p m = case m of
  Method name []      -> string name
  MethodModified m mm -> (parens $ prettyMethod p m) <> pretty mm
  _                   -> parens $ prettyMethod p m

prettyMethod :: Int -> Method -> Doc ann
prettyMethod p m = case m of
    Method name args ->
      hsep . map string $ name:args
    MethodModified m' mm -> prettyMethodTopLevel p m' <> pretty mm
    MethodCompound binOp m' m'' -> 
      prettyBinOp p prettyMethod (methodBinOpRec binOp) prettyMethod m' m''
    
instance Pretty MethodModifier where
  pretty m = case m of
    MMOptional  -> string "?"
    MMOneOrMore -> string "+"
    MMGoalRestriction mbI -> brackets $ maybe empty (string . show) $ mbI

instance PrettyAnsi MethodModifier where
  ansiP = pretty

prettyDefBase :: (Pretty terms, Pretty types) => Def types terms -> Doc ann
prettyDefBase def = string "definition" <> mbSig `vcat2` indent 2 (quote (pretty (defTerm def)))
  where mbSig = case defSig def of 
                  Just sig -> empty `vcat2` indent 2 (pretty sig) `vcat2` string "where" 
                  Nothing  -> empty

instance (Pretty terms, Pretty types) => Pretty (Def types terms) where
  pretty = prettyDefBase

instance (Pretty terms, Pretty types) => PrettyAnsi (Def types terms) where
  ansiP = prettyDefBase

prettyOv specDef sig = string "overloading" <> mbSig
                  `vcat2` string "begin"
                  `vcat2` indent 2 mbDefn
                  `vcat2` string "end"
    where mbSig = case defSig specDef of 
                    Just specSig ->
                      empty
                        `vcat2` indent 2 (pretty specSig)
                          <> string " \\<equiv> "
                          <> pretty sig
                    _ -> empty
          mbDefn =
            case defSig specDef of 
              Just specSig ->
                string "definition " <> pretty specSig <> string ": " <> quote (pretty (defTerm specDef))
              _ -> empty

prettySigBase :: Pretty types => Sig types -> Doc ann
prettySigBase d = string (sigName d) <> mbTyp
  where mbTyp = case sigType d of
                  Just typ -> empty <+> string "::" <+> quote (pretty typ)
                  Nothing  -> empty

instance Pretty types => Pretty (Sig types) where
  pretty = prettySigBase

instance Pretty types => PrettyAnsi (Sig types) where
  ansiP = prettySigBase

prettyAbbrevBase :: (Pretty terms, Pretty types) => Abbrev types terms -> Doc ann
prettyAbbrevBase a = string "abbreviation" <+> mbSig `vcat2` pretty (abbrevTerm a)
  where mbSig = case abbrevSig a of 
                  Just sig -> pretty sig <+> string "where" 
                  Nothing  -> empty

instance (Pretty terms, Pretty types) => Pretty (Abbrev types terms) where
  pretty = prettyAbbrevBase

instance (Pretty terms, Pretty types) => PrettyAnsi (Abbrev types terms) where
  ansiP = prettyAbbrevBase

instance Pretty TheoryImports where
  pretty (TheoryImports is) = string "imports" <+> fillSep (map (quote . string) is)

instance PrettyAnsi TheoryImports where
  ansiP = pretty

-- improved PrettyPlus for theories

instance (PrettyPlus terms, Pretty types) =>  PrettyPlus (Theory types terms) where
  prettyPlus thy = (string "theory" <+> string (thyName thy)) `vcat2`
                         pretty (thyImports thy) `vcat2`
                         string "begin" `vcat2`
                         prettyPlusThyDecls (thyBody thy) <>
                         string "end" `vcat2` empty

prettyPlusThyDecls :: (PrettyPlus terms, Pretty types) => [TheoryDecl types terms] -> Doc ann
prettyPlusThyDecls [] = empty
prettyPlusThyDecls thyDecls = (vsepPad . map prettyPlus $ thyDecls) `vcat2` empty

-- only the printing of terms in definitions is modified

instance (PrettyPlus terms, Pretty types) => PrettyPlus (TheoryDecl types terms) where
  prettyPlus d = case d of
    Definition def      -> prettyPlus def
    OverloadedDef def sig -> prettyOv def sig
    Abbreviation abbrev -> pretty abbrev
    ContextDecl c       -> pretty c
    LemmaDecl d'        -> pretty d'
    LemmasDecl ld       -> pretty ld
    TypeSynonym ts      -> pretty ts
    TypeDeclDecl td     -> pretty td
    ConstsDecl c        -> pretty c
    RecordDecl fs       -> pretty fs
    DataTypeDecl dt     -> pretty dt
    FunFunction ff f    -> (if ff then string "fun" else string "function") <+> pretty f
    TheoryString s      -> string s

instance (PrettyPlus terms, Pretty types) => PrettyPlus (Def types terms) where
  prettyPlus def = string "definition" <> mbSig `vcat2` indent 2 (quote (prettyPlus (defTerm def)))
    where mbSig = case defSig def of 
                    Just sig -> empty `vcat2` indent 2 (pretty sig) `vcat2` string "where" 
                    Nothing  -> empty

-- smart constructor

mkComment :: String -> TheoryDecl types terms
mkComment s = TheoryString $ "(* " ++ s ++ " *)"

