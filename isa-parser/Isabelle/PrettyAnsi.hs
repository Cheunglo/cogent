module Isabelle.PrettyAnsi where

import Control.Applicative
import Data.Int
import Data.List.NonEmpty (NonEmpty (..))
import Data.Maybe
import Data.String (IsString (..))
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Lazy as Lazy
import Data.Void
import Data.Word
import Prettyprinter
import Prettyprinter.Render.Terminal
import System.IO

class PrettyAnsi a where
    ansiP :: a -> Doc AnsiStyle
    ansiPList :: [a] -> Doc AnsiStyle
    ansiPList = align . list . map ansiP
    {-# MINIMAL ansiP #-}

--instance PrettyAnsi (Doc ann) where
--    ansiP = id

instance PrettyAnsi a => PrettyAnsi (Const a b) where
    ansiP = ansiP . getConst

#if FUNCTOR_IDENTITY_IN_BASE
instance PrettyAnsi a => PrettyAnsi (Identity a) where
    ansiP = ansiP . runIdentity
#endif

instance PrettyAnsi a => PrettyAnsi [a] where
    ansiP = ansiPList

instance PrettyAnsi a => PrettyAnsi (NonEmpty a) where
    ansiP (x:|xs) = ansiPList (x:xs)

instance PrettyAnsi () where
    ansiP = pretty

instance PrettyAnsi Bool where
    ansiP = pretty

instance PrettyAnsi Char where
    ansiP = pretty

#ifdef MIN_VERSION_text
    ansiPList = ansiP . (id :: Text -> Text) . fromString
#else
    ansiPList = vsep . map unsafeTextWithoutNewlines . T.splitOn "\n"
#endif


instance PrettyAnsi Int    where ansiP = pretty
instance PrettyAnsi Int8   where ansiP = pretty
instance PrettyAnsi Int16  where ansiP = pretty
instance PrettyAnsi Int32  where ansiP = pretty
instance PrettyAnsi Int64  where ansiP = pretty
instance PrettyAnsi Word   where ansiP = pretty
instance PrettyAnsi Word8  where ansiP = pretty
instance PrettyAnsi Word16 where ansiP = pretty
instance PrettyAnsi Word32 where ansiP = pretty
instance PrettyAnsi Word64 where ansiP = pretty

instance PrettyAnsi Integer where ansiP = pretty

#if NATURAL_IN_BASE
instance PrettyAnsi Natural where ansiP = pretty
#endif

instance PrettyAnsi Float where ansiP = pretty

instance PrettyAnsi Double where ansiP = pretty

instance (PrettyAnsi a1, PrettyAnsi a2) => PrettyAnsi (a1,a2) where
    ansiP (x1,x2) = tupled [ansiP x1, ansiP x2]

instance (PrettyAnsi a1, PrettyAnsi a2, PrettyAnsi a3) => PrettyAnsi (a1,a2,a3) where
    ansiP (x1,x2,x3) = tupled [ansiP x1, ansiP x2, ansiP x3]

instance PrettyAnsi a => PrettyAnsi (Maybe a) where
    ansiP = maybe mempty ansiP
    ansiPList = ansiPList . catMaybes

#ifdef MIN_VERSION_text
instance PrettyAnsi Text where ansiP = pretty

instance PrettyAnsi Lazy.Text where ansiP = ansiP . Lazy.toStrict
#endif

instance PrettyAnsi Void where ansiP = pretty

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
--infixr 5 </>,<//>,<$>,<$$>
infixr 5 `fillSep2`
infixr 5 `fillCat2`
infixr 5 `vsep2`
infixr 5 `vcat2`

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

renderSmart :: Double -> Int -> Doc ann -> SimpleDocStream ann
renderSmart x y = layoutSmart LayoutOptions { layoutPageWidth = AvailablePerLine y x }

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
