{-  Title:      Tools/Haskell/File.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

File-system operations
-}

module Isabelle.File (setup, read, write, append) where

import Prelude hiding (read)
import System.IO (IO)
import qualified System.IO as IO
    
setup :: IO.Handle -> IO ()
setup h = do
  IO.hSetEncoding h IO.utf8
  IO.hSetNewlineMode h IO.noNewlineTranslation

read :: IO.FilePath -> IO String
read path =
  IO.withFile path IO.ReadMode (\h ->
    do setup h; IO.hGetContents h >>= \s -> length s `seq` return s)

write :: IO.FilePath -> String -> IO ()
write path s =
  IO.withFile path IO.WriteMode (\h -> do setup h; IO.hPutStr h s)

append :: IO.FilePath -> String -> IO ()
append path s =
  IO.withFile path IO.AppendMode (\h -> do setup h; IO.hPutStr h s)
