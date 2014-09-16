{-
- Module to parse Lisp
-  
-
- Copyright 2013 -- name removed for blind review, all rights reserved! Please push a git request to receive author's name! --
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
{-# OPTIONS_GHC -Wall #-}
module LispParser (pGetLisp,parse,LispTree(..),LispPrimitive(..),SourcePos) where
import Text.ParserCombinators.Parsec (getPosition,SourcePos,parse,space,spaces,many,string,(<|>),Parser,noneOf,anyChar,unexpected,oneOf,digit,(<?>),eof)
import Data.Char (toUpper)

data LispTree = LispCons SourcePos LispTree LispTree | LispTreePrimitive SourcePos LispPrimitive deriving (Show)
data LispPrimitive = LispInt Int | LispString String | LispSymbol String deriving (Eq,Show)
         
pGetLisp :: Parser [LispTree]
pGetLisp
 = do spaces
      e<-many lispTree
      _<-eof
      return (e)
  where
   lispTree :: Parser LispTree
   lispTree
    = do { pos<-getPosition ;
              do{_<-string "(";spaces;lts<-innerLispTree pos;_<-string ")";spaces;return lts} <|>
              do{_<-string "'";spaces;lt<-lispTree;spaces;return$ LispCons pos (LispTreePrimitive pos$ LispSymbol "QUOTE") (LispCons pos lt $ LispTreePrimitive pos $ LispSymbol "NIL")} <|>
              do{p<-lispPrimitive;spaces;return$ LispTreePrimitive pos p} <?> "LISP expression"
              }
   innerLispTree pos = do{_<-string ".";_<-space <?> "space. Symbols starting with . should be enclosed in ||'s";spaces;lt<-lispTree;spaces;return lt}
                       <|> do{lt <- lispTree;spaces;rt<-innerLispTree pos;spaces;return$ LispCons pos lt rt} <|> (return$ LispTreePrimitive pos$LispSymbol "NIL")
   lispPrimitive :: Parser LispPrimitive
   lispPrimitive
    =  do{_<-string "\""; str<-lp "\""; return$ LispString str} <|> 
       -- note: we are a bit stricter on digits: any symbol starting with a digit, should be an integer
       do{d<-digit; s<-many digit; return (LispInt (read$ d:s))} <|>
       -- we also fail on any of these:
       do{_<-oneOf "-;#\\.`"; unexpected "character. Symbols starting with . - ; \\ ` or # should be enclosed in ||'s"} <|>
       do{s<-symb; return$LispSymbol s}
       where lp s = do{_<-string s; return ""} <|> do{_<-string "\\"; c<-anyChar; r<-lp s; return (c:r)} <|> do{c<-anyChar; r<-lp s; return (c:r)} <?> "end of "++s++"-delimited string"
             symb :: Parser String
             symb = do{_<-string "|"; p<-lp "|"; r<-symb <|> (return ""); return$ p++r} <|>
                    do{c<-noneOf " \t\r\n()|;#"; r<-symb <|> (return ""); return$ (toUpper c):r}
