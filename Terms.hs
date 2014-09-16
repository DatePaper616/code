{-# OPTIONS_GHC -Wall -}
{-
- Module about terms. Used after parsing eMOD
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
module Terms(Term(..),(.+.)) where
import qualified Data.Set as Set

data Term = T_AND Term Term | T_OR Term Term | T_NOT Term | T_XOR Term Term | T_ITE Term Term Term
          | T_QTRDY String | T_QIRDY String | T_QDATA String Int
          | T_OTRDY String | T_IIRDY String | T_IDATA String Int
          | T_FLOPV String | T_RESET
          | T_UNKNOWN Int
          | T_INPUT String -- same as unknown, only named
          | T_VALUE Bool
          deriving (Eq,Ord,Show)

type TermSet = Set.Set Term
(.+.) :: TermSet -> TermSet -> TermSet
(.+.) = Set.union