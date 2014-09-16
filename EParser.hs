{-# OPTIONS_GHC -Wall -}
{-
- Module to parse .emod files
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
module EParser(parse,tbrfun,pGetEMOD,pGetLisp,pGetTerms,LispTree(..),TermBuilder (..)
  ,QueueAssignment(..),FlopAssignment(..),InputAssignment(..),OutputAssignment(..),Term(..)
  ,OutputWire(..),names,HasName(name),AssignmentOrWire(..)) where

import LispParser (parse,pGetLisp,LispTree(..),LispPrimitive(..),SourcePos)
import Terms(Term(..),(.+.))
import qualified Data.Set as Set (fromList, singleton)

type EStructure = ([QueueAssignment],[FlopAssignment],[InputAssignment],[OutputAssignment],[OutputWire])
-- lisp terms without lambda functions, since we do not use lambda functions in E
data LispTerm = LispTerm SourcePos String [LispTerm] | LispTermPrimitive SourcePos LispPrimitive deriving (Show)
data GetTermError = GetTermError String SourcePos

data QueueAssignment = QueueAssignment String -- | Queue name
                                       Int    -- | Queue size
                                       Term   -- | input-channel irdy
                                       [Term] -- | input-channel data
                                       Term   -- | output-channel trdy
                                       deriving Show
data FlopAssignment = FlopAssignment String -- | register name
                                     Term   -- | register value
                                     deriving Show
data InputAssignment = InputAssignment String -- | input name
                                       Term   -- | trdy value
                                       deriving Show
data OutputAssignment = OutputAssignment String -- | output name
                                         Term   -- | irdy value
                                         [Term] -- | data value
                                         deriving Show
data OutputWire = OutputWire String Term deriving Show
data AssignmentOrWire = AssignQ QueueAssignment | AssignF FlopAssignment | AssignI InputAssignment | AssignO OutputAssignment | Wire OutputWire

class HasName a where
 name :: a -> String

instance HasName QueueAssignment where
 name (QueueAssignment n _ _ _ _) = n
instance HasName FlopAssignment where
 name (FlopAssignment n _) = n
instance HasName InputAssignment where
 name (InputAssignment n _) = n
instance HasName OutputAssignment where
 name (OutputAssignment n _ _) = n
instance HasName OutputWire where
 name (OutputWire n _) = n

names :: (HasName a) => [a] -> [String]
names = map name

sortOutAssignments :: [AssignmentOrWire] -> ([QueueAssignment],[FlopAssignment],[InputAssignment],[OutputAssignment],[OutputWire])
sortOutAssignments xs = ([a|AssignQ a<-xs],[a|AssignF a<-xs],[a|AssignI a<-xs],[a|AssignO a<-xs],[a|Wire a<-xs])

data TermBuilder a b = TBError a | TB b Int -- .. and warnings?
data TBR a b = TBR{tbrfun::(Int -> TermBuilder a b)}
instance Monad (TBR a) where
 return b = TBR (TB b)
 (>>=) (TBR f1) f2 = TBR (\x -> case f1 x of {TBError a -> TBError a; TB b y -> (tbrfun (f2 b)) y})

instance Show GetTermError where
 show (GetTermError s p) = s ++ "\n on "++ (show p)
 
getTermPos :: LispTerm -> SourcePos
getTermPos (LispTerm p _ _) = p
getTermPos (LispTermPrimitive p _) = p

firstLeft :: [TBR a' a] -> TBR a' [a]
firstLeft [] = return []
firstLeft (r:rs) = r >>= (\x -> tbrDo ((:) x) (firstLeft rs))

tbrDo :: (b1 -> b) -> TBR a b1 -> TBR a b
tbrDo f arg = TBR (\y -> case (tbrfun arg) y of {TBError a -> TBError a;TB b i -> TB (f b) i})

firstLeftMap :: (a1 -> TBR a b) -> [a1] -> TBR a [b]
firstLeftMap f xs = firstLeft (map f xs)

pGetTerms :: [LispTree] -> TBR GetTermError [LispTerm]
pGetTerms xs = firstLeftMap pGetTerm xs

-- data LispTree = LispCons SourcePos LispTree LispTree | LispTreePrimitive SourcePos LispPrimitive deriving (Show)
-- the TBR monoid takes failures on the left and return values on the right

pGetTerm :: LispTree -> TBR GetTermError LispTerm
pGetTerm (LispCons p a b) = do { h <- pGetSymbol a
                               ; t' <- pGetList b
                               ; t <- firstLeft (map pGetTerm t')
                               ; return (LispTerm p h t)
                               }
pGetTerm (LispTreePrimitive p p') = return (LispTermPrimitive p p')

pGetCons :: LispTree -> TBR GetTermError (LispTree, LispTree)
pGetCons (LispCons _ a b) = return (a,b)
pGetCons (LispTreePrimitive p _) = makeError p "Expecting CONS"

pGetList :: LispTree -> TBR GetTermError [LispTree]
pGetList (LispCons _ a b) = do {b' <-pGetList b;return$ a:b'}
pGetList (LispTreePrimitive _ (LispSymbol "NIL")) = return []
pGetList (LispTreePrimitive p _) = makeError p "Expecting end of list marker NIL (perhaps you should omit the . ?)"

pGetAList :: LispTree -> TBR GetTermError [(String,LispTerm)]
pGetAList x = pGetList x >>= firstLeftMap pGetAssignment

pGetEMOD :: LispTree -> TBR GetTermError ([QueueAssignment],[FlopAssignment],[InputAssignment],[OutputAssignment],[OutputWire])
pGetEMOD x = do { alist <- pGetAList x
                ; assignments <- firstLeftMap getAssignment alist
                ; return (sortOutAssignments assignments)
                }

repeatN :: Int -> (TBR GetTermError a) -> (TBR GetTermError [a])
repeatN n f = if n<=0 then return [] else do{v<-f;r<-repeatN (n-1) f;return (v:r)}

getAssignment :: (String,LispTerm) -> TBR GetTermError AssignmentOrWire
getAssignment (name,LispTerm p "FLOP" lts)
 = case lts of { (clk : LispTermPrimitive _ (LispSymbol name') : val : [])
                 -> do{ trm <- getTerm val
                      ; _ <- getClk clk
                      ; _ <- (if name/=name' then makeError p ("the name in the flop should be itself: "++name++" /= "++name')
                                             else return ())
                      ; return$ AssignF (FlopAssignment name trm)
                      }
               ; _ -> makeError p "FLOP should have the arguments: |clk| name value, where name must be a symbol."
               }
getAssignment (name,LispTerm p "GET-QUEUE-STATE" lts)
 = case lts of { (LispTermPrimitive _ (LispInt size) : LispTermPrimitive _ (LispInt dsize) : irdy : d : trdy : [])
                 -> do{ irdy' <- getTerm irdy
                      ; d' <- getData d
                      ; trdy' <- getTerm trdy
                      ; unknowns <- (repeatN (dsize - length d') (getTerm (LispTerm p "X" [])))
                      ; return$ AssignQ (QueueAssignment name size irdy' (d'++unknowns) trdy')
                      }
               ; _ -> makeError p "QUEUE should have the arguments: size data-size irdy data trdy, where size and data-size are integers"}
getAssignment (name,LispTerm p "GET-SOURCE-STATE" lts)
 = case lts of { (trdy : [])
                 -> do{ trdy' <- getTerm trdy
                      ; return$ AssignI (InputAssignment name trdy')
                      }
               ; _ -> makeError p "SOURCE should have one argument: trdy"}
getAssignment (name,LispTerm p "GET-SINK-STATE" lts)
 = case lts of { (irdy : d : [])
                 -> do{ d' <- getData d
                      ; irdy' <- getTerm irdy
                      ; return$ AssignO (OutputAssignment name irdy' d')
                      }
               ; _ -> makeError p "SINK should have two argument: irdy data"}
getAssignment (name,LispTerm p "OUTPUT" lts)
 = case lts of { (irdy : [])
                 -> do{ irdy' <- getTerm irdy
                      ; return$ Wire (OutputWire name irdy')
                      }
               ; _ -> makeError p "OUTPUT should have one argument: the term it represents"}
getAssignment (name,t)
  = makeError (getTermPos t)
              ("Not a valid assignment for "++name++",\n  should be either FLOP, OUTPUT or GET-*-STATE where * = SINK, SOURCE or QUEUE")

getData :: LispTerm -> TBR GetTermError [Term]
getData (LispTerm _ "LIST" lst)
 = firstLeftMap getTerm lst
getData (LispTerm _ "X" [])
 = return [] -- cheat a little by putting X this way
getData t = makeError (getTermPos t)
              ("Not a valid list, lists should start with the function symbol LIST")

getTerm :: LispTerm -> TBR GetTermError Term
getTerm (LispTerm p "AND" lst) = do {(a,b)<-get2 p "arguments for AND" lst;a'<-getTerm a;b'<-getTerm b;return (T_AND a' b')}
getTerm (LispTerm p "OR" lst) = do {(a,b)<-get2 p "arguments for OR" lst;a'<-getTerm a;b'<-getTerm b;return (T_OR a' b')}
getTerm (LispTerm p "NOT" lst) = do {a<-get1 p "argument for NOT" lst;a'<-getTerm a;return (T_NOT a')}
getTerm (LispTerm p "XOR" lst) = do {(a,b)<-get2 p "arguments for OR" lst;a'<-getTerm a;b'<-getTerm b;return (T_XOR a' b')}
getTerm (LispTerm p "FLOPVAL" lst)
 = do {(a,b)<-get2 p "arguments for FLOPVAL" lst;_<-getClk a;b'<-getSymbol b;return (T_FLOPV b')}
getTerm (LispTerm p "VALUE" lst)
 = case lst of { (LispTermPrimitive _ (LispSymbol "O.IRDY") : LispTermPrimitive _ (LispSymbol s) : []) -> return$ T_QIRDY s
               ; (LispTermPrimitive _ (LispSymbol "I.TRDY") : LispTermPrimitive _ (LispSymbol s) : []) -> return$ T_QTRDY s
               ; (LispTermPrimitive _ (LispSymbol "O.DATA") : LispTermPrimitive _ (LispInt i) : LispTermPrimitive _ (LispSymbol s) : []) -> return$ T_QDATA s i
               ; (LispTermPrimitive _ (LispSymbol "S.IRDY") : LispTermPrimitive _ (LispSymbol s) : []) -> return$ T_IIRDY s
               ; (LispTermPrimitive _ (LispSymbol "S.TRDY") : LispTermPrimitive _ (LispSymbol s) : []) -> return$ T_OTRDY s
               ; (LispTermPrimitive _ (LispSymbol "S.DATA") : LispTermPrimitive _ (LispInt i) : LispTermPrimitive _ (LispSymbol s) : []) -> return$ T_IDATA s i
               ; _ -> makeError p "VALUE should either get O.IRDY, I.TRDY or O.DATA with a queue-name (or an integer + queue name for O.DATA), or S.* similarly"
               }
getTerm (LispTerm p "X" lst) = do {_<-get0 p "arguments for X" lst;increment (\x -> T_UNKNOWN x)}
getTerm (LispTerm p "F" lst) = do {_<-get0 p "arguments for F" lst;return (T_VALUE False)}
getTerm (LispTerm p "T" lst) = do {_<-get0 p "arguments for T" lst;return (T_VALUE True)}
getTerm (LispTermPrimitive p p') = do {_<-getRst p p';return T_RESET}
getTerm (LispTerm p "INPUT" lst) = do {a<-get1 p "argument for INPUT" lst;a'<-getSymbol a;return (T_INPUT a')}
getTerm (LispTerm p s _) = makeError p ("unexpected function symbol: "++s++"\n  Recognised function symbols are: AND, OR, NOT, XOR, FLOPVAL, INPUT and VALUE")

-- like return, only allows for an integer too
increment :: (Int -> b) -> TBR a b
increment f = (TBR (\x -> TB (f x) (x + 1)))

getRst :: SourcePos -> LispPrimitive -> TBR GetTermError ()
getRst _ (LispSymbol "rst") = return ()
getRst p _ = makeError p "the only free symbol allowed is the reset: |rst|"

getClk :: LispTerm -> TBR GetTermError ()
getClk (LispTermPrimitive _ (LispSymbol "clk")) = return ()
getClk t = makeError (getTermPos t) "expecting clock symbol |clk|"

get2 :: SourcePos -> [Char] -> [t] -> TBR GetTermError (t, t)
get2 _ _ (a:b:[]) = return (a,b)
get2 p s _ = makeError p ("Expecting two "++s)
get1 :: SourcePos -> [Char] -> [a] -> TBR GetTermError a
get1 _ _ (a:[]) = return a
get1 p s _ = makeError p ("Expecting one "++s)
get0 :: SourcePos -> [Char] -> [a] -> TBR GetTermError ()
get0 _ _ [] = return ()
get0 p s _ = makeError p ("Expecting no "++s)

(<?>) :: TBR GetTermError b -> String -> TBR GetTermError b
(<?>) tbr msg = TBR (\x -> case (tbrfun tbr) x of {TBError (GetTermError _ p) -> makeError' msg p;v -> v})

pGetAssignment :: LispTree -> TBR GetTermError (String,LispTerm)
pGetAssignment x = do { (a,b) <- (pGetCons x <?> "Expecting assignment")
                      ; s <- pGetSymbol a <?> "Assignment requires its first item to be a symbol"
                      ; t <- pGetTerm b
                      ; return (s,t) }

makeError :: SourcePos -> String -> TBR GetTermError b
makeError pos str = TBR (\_ -> makeError' str pos)

makeError' :: String -> SourcePos -> TermBuilder GetTermError b
makeError' str pos = TBError (GetTermError str pos)

getSymbol :: LispTerm -> TBR GetTermError String
getSymbol (LispTermPrimitive _ (LispSymbol p)) = return$ p
getSymbol (LispTermPrimitive p _) = makeError p "Expecting primitive of Symbol type, consider putting ||'s around the primitive"
getSymbol (LispTerm p _ _) = makeError p "Expecting primitive of Symbol type, got a Cons"

pGetSymbol :: LispTree -> TBR GetTermError String
pGetSymbol (LispTreePrimitive _ (LispSymbol p)) = return$ p
pGetSymbol (LispTreePrimitive p _) = makeError p "Expecting primitive of Symbol type, consider putting ||'s around the primitive"
pGetSymbol (LispCons p _ _) = makeError p "Expecting primitive of Symbol type, got a Cons"
