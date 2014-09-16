{-# OPTIONS_GHC -Wall -XFlexibleInstances #-}
{-
-  
- Copyright 2014 -- name removed for blind review, all rights reserved! Please push a git request to receive author's name! --
- Licensed under the Apache License, Version 2.0 (the "License");
-  you may not use this file except in compliance with the License.
-  You may obtain a copy of the License at
-
-      http://www.apache.org/licenses/LICENSE-2.0
-
-  Unless required by applicable law or agreed to in writing, software
-  distributed under the License is distributed on an "AS IS" BASIS,
-  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
-  See the License for the specific language governing permissions and
-  limitations under the License.
-}
module Main (main) where
import System.Environment (getArgs)
import EParser (parse,tbrfun,pGetEMOD,pGetLisp,TermBuilder (..))
import ToNET   (showNET)
import           System.IO

main :: IO ()
main
 = do args <- getArgs
      s <- readContents args "i"
      case (parse pGetLisp "(stdin)" s) of
        (Left e) -> hPutStrLn stderr (show e)
        (Right [g]) -> case (tbrfun (pGetEMOD g) 0) of
                      (TBError e) -> hPutStrLn stderr (show e)
                      (TB v _) -> do let (dotGraph,proofObligations) = showNET v
                                     write args "g" dotGraph
                                     write args "p" proofObligations
        (Right []) -> hPutStrLn stderr "Please supply input at (stdin)"
        _ -> hPutStrLn stderr "More than one input not supported"

readContents :: [String] -> String -> IO (String)
readContents (('-':h):v:_) h' | h==h'
 = case v of
    "-" -> getContents
    "_" -> return ""
    f -> do hd <- openFile f ReadMode
            hGetContents hd
readContents (_:as) x = readContents as x
readContents [] f
 = do hPutStrLn stderr$ "No `-"++f++" filename' argument given, using stdin for input (use - as a filename to suppress this warning while still using stdin, or _ to read an empty string)."
      getContents
write :: [String] -> String -> String -> IO ()
write (('-':h):v:_) h' s | h==h'
 = case v of
    "-" -> putStrLn s
    "_" -> return ()
    f -> do hd <- openFile f WriteMode
            hPutStrLn hd s
            hClose hd
write (_:as) x y = write as x y
write [] f _ = hPutStrLn stderr$ "No `-"++f++" filename' argument given, some of the output is omitted (use - as a filename for stdout, or _ to suppress this warning)."