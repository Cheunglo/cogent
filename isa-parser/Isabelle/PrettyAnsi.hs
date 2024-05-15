module Isabelle.PrettyAnsi where

import Prettyprinter
import Prettyprinter.Render.Terminal

type DocAnsi = Doc AnsiStyle

class (Pretty a) => (PrettyAnsi a) where
    prettyAnsi :: a -> DocAnsi
    prettyAnsi x = pretty x

char :: Char -> Doc ann
char c = pretty c

text :: String -> Doc ann
text s = pretty s

string :: String -> Doc ann
string s = pretty s

int :: Int -> Doc ann
int i = pretty i

integer :: Integer -> Doc ann
integer i = pretty i

empty :: Doc ann
empty = emptyDoc

-- <$>, <$$>, </>, <//> are special cases of vsep, vcat, fillSep, fillCat with only two documents.

-- <$> == \x y -> vsep [x, y]
vsep2 :: Doc ann -> Doc ann -> Doc ann
vsep2 x y = vsep [x, y]

-- <$$> == \x y -> vcat [x, y]
vcat2 :: Doc ann -> Doc ann -> Doc ann
vcat2 x y = vcat [x, y]

-- </> == \x y -> fillSep [x, y]
fillSep2 :: Doc ann -> Doc ann -> Doc ann
fillSep2 x y = fillSep [x, y]

-- <//> == \x y -> fillCat [x, y]
fillCat2 :: Doc ann -> Doc ann -> Doc ann
fillCat2 x y = fillCat [x, y]


