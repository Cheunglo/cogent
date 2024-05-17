module Isabelle.PrettyAnsi where

import Prettyprinter
import Prettyprinter.Render.Terminal
import System.IO

class (Pretty a) => (PrettyAnsi a) where
    prettyAnsi :: a -> Doc AnsiStyle
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

plain :: Doc ann -> Doc ann'
plain = unAnnotate

displayIO :: Handle -> SimpleDocStream AnsiStyle -> IO ()
displayIO = renderIO

renderPretty :: Double -> Int -> Doc ann -> SimpleDocStream ann
renderPretty x y = layoutSmart LayoutOptions { layoutPageWidth = AvailablePerLine y x }

annBf :: Doc AnsiStyle -> Doc AnsiStyle
annBf = annotate bold

annIt :: Doc AnsiStyle -> Doc AnsiStyle
annIt = annotate italicized

annUl :: Doc AnsiStyle -> Doc AnsiStyle
annUl = annotate underlined

annColor :: Color -> Doc AnsiStyle -> Doc AnsiStyle
annColor c = annotate (color c)

annColorDull :: Color -> Doc AnsiStyle -> Doc AnsiStyle
annColorDull c = annotate (colorDull c)

annBgColor :: Color -> Doc AnsiStyle -> Doc AnsiStyle
annBgColor c = annotate (bgColor c)

annBgColorDull :: Color -> Doc AnsiStyle -> Doc AnsiStyle
annBgColorDull c = annotate (bgColorDull c)

--Black	 
black :: Doc AnsiStyle -> Doc AnsiStyle
black = annColor Black

dullblack :: Doc AnsiStyle -> Doc AnsiStyle
dullblack = annColorDull Black

--Red	 
red :: Doc AnsiStyle -> Doc AnsiStyle
red = annColor Red

dullred :: Doc AnsiStyle -> Doc AnsiStyle
dullred = annColorDull Red

--Green	 
green :: Doc AnsiStyle -> Doc AnsiStyle
green = annColor Green

dullgreen :: Doc AnsiStyle -> Doc AnsiStyle
dullgreen = annColorDull Green

--Yellow	 
yellow :: Doc AnsiStyle -> Doc AnsiStyle
yellow = annColor Yellow

dullyellow :: Doc AnsiStyle -> Doc AnsiStyle
dullyellow = annColorDull Yellow

--Blue	 
blue :: Doc AnsiStyle -> Doc AnsiStyle
blue = annColor Blue

dullblue :: Doc AnsiStyle -> Doc AnsiStyle
dullblue = annColorDull Blue

--Magenta	 
magenta :: Doc AnsiStyle -> Doc AnsiStyle
magenta = annColor Magenta

dullmagenta :: Doc AnsiStyle -> Doc AnsiStyle
dullmagenta = annColorDull Magenta

--Cyan	 
cyan :: Doc AnsiStyle -> Doc AnsiStyle
cyan = annColor Cyan

dullcyan :: Doc AnsiStyle -> Doc AnsiStyle
dullcyan = annColorDull Cyan

--White
white :: Doc AnsiStyle -> Doc AnsiStyle
white = annColor White

dullwhite :: Doc AnsiStyle -> Doc AnsiStyle
dullwhite = annColorDull White
