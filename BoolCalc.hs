{-# OPTIONS_GHC -Wall #-}
module BoolCalc (booleanEquiv,booleanFalse,zeroMap,oneMap,resetMap,combineOr,combineITE,combineAnd,combineXOR,combineNot,combineAtom,BooleanExpr,propToSMV) where
import qualified Data.Map.Lazy as Map
import qualified Data.Set as Set


propToSMV :: BooleanExpr -> (String, Set.Set String)
propToSMV (BE _ e st) = (e,st)

-- calculations with booleans.. these could also be done using BDD's or SAT
-- here we chose arithmetic sum of product notations
data BooleanExpr = BE (Map.Map (Set.Set String) Int) String (Set.Set String)

(.*.) :: Int -> Map.Map a Int -> Map.Map a Int 
(.*.) x y = Map.map ((*) x) y
(.-.),(.+.) :: Ord a => Map.Map a Int -> Map.Map a Int -> Map.Map a Int
(.-.) = Map.mergeWithKey (\_ a b->case a-b of {0->Nothing;s->Just s}) id (Map.map (\x -> -x))
(.+.) = Map.mergeWithKey (\_ a b->case a+b of {0->Nothing;s->Just s}) id id

booleanEquiv :: BooleanExpr -> BooleanExpr -> Bool
booleanEquiv (BE a _ _) (BE b _ _) = a == b

booleanFalse :: BooleanExpr -> Bool -- true if the expression is False
booleanFalse (BE a _ _) = Map.null a

zeroMap,oneMap,resetMap :: BooleanExpr
zeroMap = BE (Map.empty) "FALSE" Set.empty
oneMap = BE (Map.singleton Set.empty 1) "TRUE" Set.empty
resetMap = BE (Map.singleton Set.empty 1) "resetBit" Set.empty

combineAtom :: String -> BooleanExpr
combineAtom x = BE (Map.singleton (Set.singleton x) 1) x (Set.singleton x)

combineNot :: BooleanExpr -> BooleanExpr
combineNot (BE a as aitms) = (BE (combineNotMap a) ("!"++as) aitms)
combineNotMap :: Ord a => Map.Map (Set.Set a) Int -> Map.Map (Set.Set a) Int
combineNotMap a = Map.singleton Set.empty 1 .-. a

combineOr, combineXOR :: BooleanExpr -> BooleanExpr -> BooleanExpr
combineOr (BE a as aitms) (BE b bs bitms) = BE (a .+. b .-. combineAndMap a b) ("("++as++" | "++bs++")") (Set.union aitms bitms)
combineXOR (BE a as aitms) (BE b bs bitms) = BE (a .+. b .-. (2 .*. combineAndMap a b)) ("("++as++" xor "++bs++")") (Set.union aitms bitms)

combineITE :: BooleanExpr -> BooleanExpr -> BooleanExpr -> BooleanExpr
combineITE (BE a as aitms) (BE b bs bitms) (BE c cs citms)
 = BE (combineAndMap a b .+. combineAndMap (combineNotMap a) c) ("("++ as++" ? "++bs++" : "++cs++")") (Set.unions [aitms,bitms,citms])
-- "combineAnd" would be a nice candidate to prove correct in ACL2
combineAnd :: BooleanExpr -> BooleanExpr -- two LPs for which the AND must be calculated
           -> BooleanExpr -- result
-- this is just some sort of Cartesian product
combineAnd (BE a as aitms) (BE b bs bitms)
  = BE (combineAndMap a b) ("("++as++" & "++bs++")") (Set.union aitms bitms)
combineAndMap :: (Eq a, Num a, Ord a1) =>
                       Map.Map (Set.Set a1) a
                       -> Map.Map (Set.Set a1) a -> Map.Map (Set.Set a1) a
combineAndMap a b
 = Map.filter ((/=) 0) $ 
        Map.fromListWith (+) [(Set.union a' b', ai*bi) | (a',ai) <- Map.toList a, (b',bi) <- Map.toList b]
       