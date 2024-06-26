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

module Cogent.TypeCheck.Solver.Util where

import Cogent.TypeCheck.Base
import Cogent.TypeCheck.Solver.Goal
import Cogent.TypeCheck.Solver.Rewrite
import Cogent.TypeCheck.Util

import Control.Applicative
import Control.Monad.IO.Class
import Control.Monad.Trans.Maybe
--import qualified Text.PrettyPrint.ANSI.Leijen as P
--import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>), (<>), empty)
import qualified Prettyprinter as P
import           Prettyprinter hiding ((<>))
import           Isabelle.PrettyAnsi hiding (empty)      

debug :: (MonadIO m) => String -> (a -> String) -> RewriteT m a -> RewriteT m a
debug  nm p rw = rw `andThen` debugPass ("After " ++ nm ++ ":") p

debugL :: (MonadIO m) => String -> (a -> String) -> Rewrite a -> RewriteT m a
debugL nm p rw = debug nm p (lift rw)

debugF :: (MonadIO m) => String -> (a -> String) -> RewriteT m a
debugF nm = debugFail ("=== " ++ nm ++ " ===")

printC :: [Goal] -> String
printC gs =
 let gs' = map (P.nest 2 . ansiP . _goal) gs
 in show (P.line P.<> P.indent 2 (P.list gs'))

printPretty :: (PrettyAnsi a) => a -> String
printPretty = show . ansiP


-- | For debugging, prints the contents of the rewrite to the console, with a string prefix.
--   Returns empty result and counts as no progress.
debugFail :: (MonadIO m) => String -> (a -> String) -> RewriteT m a
debugFail pfx show = RewriteT (\cs -> traceTc "rewrite" (text pfx `vcat2` text (show cs)) >> empty)

-- | Print debugging information as above, but counts as a successful rewrite.
--   Useful for putting debugging after another rewrite, if you only want to print on success.
debugPass :: (MonadIO m) => String -> (a -> String) -> RewriteT m a
debugPass pfx show = RewriteT (\cs -> traceTc "rewrite" (text pfx `vcat2` text (show cs)) >> return cs)

-- | Print debugging information as above, but counts as a successful rewrite.
--   Useful for putting debugging after another rewrite, if you only want to print on success.
debugStr :: (Monad m, MonadIO m) => String -> String -> RewriteT m a
debugStr ctx msg = RewriteT (const $ traceTc ctx (text msg) >> empty)

