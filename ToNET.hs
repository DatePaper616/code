{-# OPTIONS_GHC -Wall #-}
{-
cat eMODFiles/bufferedVC.emod | ./eMOD -i - -g _ -p - | ./nuXmv
cat eMODFiles/bufferedVC.emod | ./eMOD -i - -g - -p _ | dot -obufferedVC.pdf -Tpdf
cat eMODFiles/2entryExplicit.emod | ./eMOD -i - -g _ -p - | ./nuXmv
cat eMODFiles/2entryExplicit.emod | ./eMOD -i - -g - -p _ | dot -o2entryscoreboard.pdf -Tpdf
-}
module ToNET (showNET)  where
import Terms (Term(..))
import qualified Data.Set as Set
import Data.List (partition)
import BoolCalc
import EParser (QueueAssignment(..),FlopAssignment(..),InputAssignment(..),OutputAssignment(..)
               ,OutputWire(..),HasName(name))

-- Properties from a list of queue information
-- Only the p_r and p_s properties are extracted here
extractProperties :: [QueueAssignment]
                  -> ( [(Int, QueueAssignment)]
                     , [(NetworkTree x, BooleanExpr, BooleanExpr)])
extractProperties qi
 = ( queues
   , concat [ [ (Q i Up,qs,readys), (Q i Down,qt,readyt) ]
            | (i,q) <- queues, let ((qs,readys),(qt,readyt)) = obtainQueue q]
   )
 where queues = zip [0..] qi

mergeProperties :: ([(NetworkTree (), BooleanExpr, BooleanExpr)])
                -> ([NetworkTree ValUpDown])
-- mergeProperties does not touch the queue part..
-- first we iterate over the "open" properties
-- this is not the most efficient implementation, but it does the job
mergeProperties p
 = case mergeOptions p [] of
     Nothing -> map finalStep p
     Just v -> mergeProperties v -- try another step, this fixpoint can be made more efficient as multiple iterations of findEqs can be combined into one
 where
  mergeOptions [] _ = sumOptions p []
  mergeOptions (o@(v,fullProp,defaultProp):as) rest
   = if null as' then mergeOptions as (o:rest) else 
     Just ( ( NT SynT () (unwrap (v:map (\(v',_,_)->v') as'))
            , fullProp, foldr combineAnd defaultProp (map (\(_,_,dp) -> dp) as')
            ) : remaining )
   where (as',r') = partition (\(_,fp',_) -> fullProp `booleanEquiv` fp') as
         remaining = rest ++ r'
  unwrap (NT SynT _ lst : rst ) = lst ++ unwrap rst -- we known lst is already `unwrapped'
  unwrap (x : rst ) = x : unwrap rst
  unwrap [] = []
  -- in sumOptions, we would like to discover the arbitration policy, that is:
  -- what is the simplest property p such that
  -- p /\ (a \/ a') = a
  -- obviously p=a and p=-a' will do, but they are not the same
  -- let's take the (linear) line between them:
  -- p = xa .+. (1.-.x)(-a') = xa .+. (1 .-. x) (1 .-. a') = x(a .+. a') .+. 1 .-. x .-. a'
  -- reasoning in booleans: for x=true we get p=a, for x=false we get p=-a'
  --   so any boolean expression for x results in p /\ (a \/ a') = a
  -- we are currently not using this technique
  sumOptions [] _ = Nothing
  sumOptions (o@(v,a,defaultProp):as) rest
   = if null result then sumOptions as (o:rest) else head result -- note: "head" is a heuristic choice here!
   where result = [ let newdefault = combineOr defaultProp dp in
                    Just ((NT (RouT a a' defaultProp dp) () [v,ref], combineOr a a', newdefault) : rest ++ pre ++ post)
                  | (pre,(ref,a',dp),post) <- splitList as, booleanFalse (combineAnd a a')]
  finalStep (nt,fullprop,defaultprop)
   = orient Down$
     if fullprop `booleanEquiv` defaultprop then nt else
     NT SynT () (P () fullprop : unwrap [nt])

orient :: ValUpDown -> NetworkTree t -> NetworkTree ValUpDown
orient d (P _ a) = P d a
orient _ (Q a b) = Q a b
orient defaultDir self@(NT (RouT a b c d) _ lst)
 = NT (RouT a b c d) newdir (map (orientAs newdir) lst) -- all children must be oriented in the same direction
 where newdir = case (deepDirection self) of
                    Nothing -> areAllEqual [o | (Just o) <- map deepDirection lst] defaultDir
                    Just x -> x
       orientAs :: ValUpDown -> NetworkTree t -> NetworkTree ValUpDown
       orientAs dir v
        = if direction id res == dir then res else (NT SynT dir [res])
        where res = orient dir v
orient defaultDir (NT SynT _ [a])
        = orient defaultDir a
orient defaultDir o@(NT SynT _ lst)
 = NT SynT
      (case dd of
        Just dir -> dir
        _ -> defaultDir)
      (zipWith orient opp lst) -- all children should be oriented in an opposite direction if possible
 where dd = deepDirection o
       opp = case dd of Nothing -> [Up,Down]++opp -- no preference; alternate!
                        Just Up -> repeat Down
                        Just Down -> repeat Up

areAllEqual :: Eq a => [a] -> a -> a
areAllEqual [] x = x
areAllEqual (a:as) x = areAllEqualTo a as x
areAllEqualTo :: Eq a => a -> [a] -> a -> a
areAllEqualTo a (a2:as) x = if a==a2 then areAllEqualTo a as x else x
areAllEqualTo a [] _ = a

deepDirection :: NetworkTree t -> Maybe ValUpDown
deepDirection (Q _ ud) = Just ud
deepDirection (P _ _) = Nothing -- (if dependsOnData (Set.toList (snd (propToSMV a))) then Just Up else Nothing)
deepDirection (NT SynT _ lst)
 = if allAs Down lst && allAs Up lst then Nothing else
   if allAs Down lst then Just Down else
   if allAs Up lst then Just Up else Nothing
 where allAs _ [] = True
       allAs v (a:as) = case deepDirection a of
                        Nothing -> allAs v as
                        (Just v') | v==v' -> allAs v as
                        _                 -> False
deepDirection (NT (RouT gu _ _ _) _ lst)
 = case (ups,downs) of
    ([],[])
     -> Just$ if dependsOnData (Set.toList (snd (propToSMV gu))) then Up else Down
    (_,[]) -> Just Up -- we care!
    ([],_) -> Just Down -- we care!
    _ -> Just$ if dependsOnData (Set.toList (snd (propToSMV gu))) then Up else Down
 where ups = [ () | Just Up <- mdl]
       downs = [ () | Just Down <- mdl]
       mdl = map deepDirection lst

dependsOnData :: [String] -> Bool
dependsOnData [] = False
dependsOnData (a:as) = if (take 4 (tail a) == "DATA") then True else dependsOnData as

data ValUpDown = Up | Down deriving (Show,Eq)

data NetworkTree x
 = NT NetComponentType x [NetworkTree x]
 | Q Int ValUpDown
 | P x BooleanExpr
data NetComponentType
 = RouT BooleanExpr -- going up
        BooleanExpr -- going down
        BooleanExpr -- up ready
        BooleanExpr -- down ready
   | SynT

accumulate :: Int -> NetworkTree t -> (NetworkTree (t, Int), Int)
accumulate i (Q a b) = (Q a b, i)
accumulate i (P x a) = (P (x,i) a, i+1)
accumulate i (NT nt x pts)
 = seq i (NT nt (x,i) res, i')
 where (res, i') = accumulateList (i+1) pts
accumulateList :: Int -> [NetworkTree t] -> ([NetworkTree (t, Int)], Int)
accumulateList i [] = ([],i)
accumulateList i (a:as) = (resA:resAs,i')
 where (resA, i'') = accumulate i a
       (resAs, i') = accumulateList i'' as

direction :: (x -> ValUpDown) -> (NetworkTree x) -> ValUpDown
direction f (NT _ ud _) = f ud
direction _ (Q _ ud) = ud
direction f (P ud _) = f ud

splitList :: [a] -> [([a],a,[a])]
splitList x = f x []
 where f [] _ = []
       f (a:as) r = (r,a,as):f as (r++[a])

showNET :: ([QueueAssignment],[FlopAssignment],[InputAssignment],[OutputAssignment],[OutputWire])
        -> (String,String)
showNET (queues',flops,_,_,_)
 = ("digraph net {" ++
    "\n  overlap=false;rankdir=TD;" ++ concat
    [ "\n  Queue"++show i++" [shape=plaintext label=<<table border=\"0\"><TR><TD><TABLE BORDER=\"1\" cellspacing=\"0\"><TR><TD PORT=\"in\">&nbsp;&nbsp;</TD></TR><TR><TD PORT=\"out\">&nbsp;</TD></TR></TABLE></TD><TD>"++name q++"</TD></TR></table>>];"
    | (i,q) <- queues ]
    ++ concat (map flatdraw' network)
    ++ "\n}\n"
   ,"MODULE main\nVAR\n" ++ concat
    [ "  "++s++" : boolean;\n" | s <- "resetBit":vars ] ++
    "ASSIGN\n  init(resetBit) := TRUE;\n  next(resetBit) := FALSE;\n" ++ concat
    [ "  next("++varName++") := "++varExpr++";\n"
    | (varName, varExpr) <- flopExprs ++ queueExprs ] ++
    concat
    [ "-- "++comment++"\n"++"LTLSPEC " ++ spec++"\n"
    | (comment,spec) <- concat assumptions ]
   )
 where connect :: String -> NetworkTree ((ValUpDown), Int) -> [Char]
       connect nm d
         = "\n    "++ (case (direction fst d) of
                        Up -> nm ++ ":s -> "++showRef d ++ ":n"
                        Down -> showRef d ++ ":s -> " ++ nm ++ ":n"
                      ) ++";"
       (assumptions,assumeVars) = unzip (map getAssumptions network)
       getAssumptions (Q _ _) = ([],Set.empty)
       getAssumptions (P (_,i) localProp) -- note: persistency is always satisfied, since localProp = transferProp
        = ( {-
            [ ( "Fairness of P" ++ show i
              , "G (resetBit | F ("++prop++"))" )
            ] -} []
          , lvars
          )
        where (prop,lvars) = propToSMV localProp
       getAssumptions (NT elemt (dir,i) lst)
        = ( cprops ++ concat rprops
          , Set.unions (cvars:rvars)
          )
        where
         (rprops,rvars) = unzip (map getAssumptions lst)
         (cprops,cvars) = case (elemt,dir) of
                            (RouT _ _ _ _, Up)   -> ([],Set.empty) -- nothing to do for a switch?
                            ( RouT p1 p2 d1 d2, Down) -> fairMerge p1 p2 d1 d2
                            _ -> ([],Set.empty)
         fairMerge p1 p2 d1 d2
          = ( [ ( "Fairness of merge "++show i++" either A is not ready in the future, A transfers in the future, or B will cease to transfer in the future."
                , "G ((F "++p1Expr++") | (F !"++d1Expr++") | (F (G !"++p2Expr++")))"
                )
              , ( "Fairness of merge "++show i++" same, but vice versa"
                , "G ((F "++p2Expr++") | (F !"++d2Expr++") | (F (G !"++p1Expr++")))"
                ) ]
            , Set.unions [p1Vars,p2Vars,d1Vars,d2Vars]
            )
          where (p1Expr,p1Vars) = propToSMV p1
                (p2Expr,p2Vars) = propToSMV p2
                (d1Expr,d1Vars) = propToSMV d1
                (d2Expr,d2Vars) = propToSMV d2
       vars = Set.toList (Set.unions$ varSetsFromFlops ++ assumeVars)
       (queueExprs,varSetsFromQueues)
        = unzip$ concat [] {-
           [ [(("QIRDY"++nm, qirdyExpr),varSetirdy)
             ,(("QTRDY"++nm, qtrdyExpr),varSettrdy)]
           | QueueAssignment nm _size inIrdy _idata ouTrdy <- queues'
           , let (qirdyExpr,varSetirdy)
                           = propToSMV$combineOr
                                       (combineAnd (combineAtom ("QIRDY"++nm))
                                                   (combineNot (translateTerm ouTrdy)))
                                       (combineAtom ("QIRDY"++nm++"ORACLE"))
           , let (qtrdyExpr,varSettrdy)
                           = propToSMV$combineOr
                                       (combineAnd (combineAtom ("QTRDY"++nm))
                                                   (combineNot (translateTerm inIrdy)))
                                       (combineAtom ("QTRDY"++nm++"ORACLE"))
           ] -}
       (flopExprs,varSetsFromFlops)
        = unzip [ (("FLOPV"++flopName,exprString),Set.insert ("FLOPV"++flopName) varSets)
                | FlopAssignment flopName flopExpr <- flops
                , let (exprString,varSets) = termToSMV flopExpr]
       showRef (Q i v) = "Queue"++show i++ case v of
                                 Up   -> ":in"
                                 Down -> ":out"
       showRef (NT _ (_,i) _) = "TP" ++ show i
       showRef (P (_,i) _) = "P"++show i
       network = fst (accumulateList 0 (mergeProperties queueProperties))
       (queues,queueProperties) = extractProperties queues'
       flatdraw' (NT SynT _ [a,b]) | direction fst a /= direction fst b
        = connect (showRef a) b ++ flatdraw a ++ flatdraw b
       flatdraw' x = flatdraw x
       flatdraw o@(NT tp _ lst)
        = "\n  "++ nm ++
          ( case tp of
             (RouT _ _ _ _) -> " [shape=none height=\"0\" label=<<table border=\"0\" cellspacing=\"0\" cellpadding=\"0\" width=\"50\" height=\"1\" FIXEDSIZE=\"true\" bgcolor=\"black\"><TR><TD></TD></TR></table>>];"
             SynT           -> " [shape=none height=\"0\" label=<<table border=\"0\" cellspacing=\"2\" cellpadding=\"0\" width=\"52\" height=\"9\" FIXEDSIZE=\"true\"><TR><TD bgcolor=\"black\" width=\"48\" height=\"1\"></TD></TR><TR><TD bgcolor=\"black\" width=\"48\" height=\"1\"></TD></TR></table>>];"
          ) ++ concat (map (connect nm) lst) ++ concat (map flatdraw lst)
        where nm = showRef o
       flatdraw _ = ""

obtainQueue :: QueueAssignment
            -> ((BooleanExpr, BooleanExpr),
                (BooleanExpr, BooleanExpr))
obtainQueue (QueueAssignment nm _size inIrdy _idata ouTrdy)
 = ((enter,translateTerm (T_QTRDY nm)),(exit,translateTerm (T_QIRDY nm)))
 where enter   = translateTerm (T_AND inIrdy (T_QTRDY nm))
       exit    = translateTerm (T_AND ouTrdy (T_QIRDY nm))

data TranslatableTerm term
 = TR_OR    term term
 | TR_XOR   term term
 | TR_ITE   term term term
 | TR_AND   term term
 | TR_NOT   term
 | TR_VALUE Bool
 | TR_RESET

translateTerm :: Term -> BooleanExpr
translateTerm t =  collectAnds combineAtom
                               translateTranslatableTerm id t

translateTranslatableTerm :: (TranslatableTerm Term)
                          -> BooleanExpr -- the resulting LP variable
translateTranslatableTerm (TR_RESET    ) = resetMap
translateTranslatableTerm (TR_VALUE b  ) = if b then oneMap
                                                else zeroMap
translateTranslatableTerm (TR_ITE a b c) = combineITE (translateTerm a) (translateTerm b) (translateTerm c)
translateTranslatableTerm (TR_OR  y1 y2) = combineOr (translateTerm y1) (translateTerm y2)
translateTranslatableTerm (TR_XOR y1 y2) = combineXOR (translateTerm y1) (translateTerm y2)
translateTranslatableTerm (TR_NOT y1   ) = combineNot (translateTerm y1)
translateTranslatableTerm (TR_AND a b)   = combineAnd (translateTerm a) (translateTerm b)

collectAnds :: (String -> t) -> (TranslatableTerm t2 -> t) -> (Term -> t2) -> Term -> t
collectAnds f _ _ (T_QTRDY x  ) = f$  "QTRDY" ++x
collectAnds f _ _ (T_QIRDY x  ) = f$  "QIRDY" ++x
collectAnds f _ _ (T_QDATA x y) = f$  "QDATA" ++x++"-"++show y
collectAnds f _ _ (T_OTRDY x  ) = f$  "OTRDY" ++x
collectAnds f _ _ (T_IIRDY x  ) = f$  "IIRDY" ++x
collectAnds f _ _ (T_IDATA x y) = f$  "IDATA" ++x++"-"++show y
collectAnds f _ _ (T_FLOPV x  ) = f$  "FLOPV" ++x
collectAnds f _ _ (T_UNKNOWN x) = f$  "UNKNO" ++show x
collectAnds f _ _ (T_INPUT x  ) = f$  "INPUT" ++x
collectAnds _ f t (T_AND x y)   = f$ TR_AND   (t x) (t y)
collectAnds _ f t (T_OR  x y)   = f$ TR_OR    (t x) (t y)
collectAnds _ f t (T_XOR x y)   = f$ TR_XOR   (t x) (t y)
collectAnds _ f t (T_ITE x y z) = f$ TR_ITE   (t x) (t y) (t z)
collectAnds _ f t (T_NOT x)     = f$ TR_NOT   (t x)
collectAnds _ f _ (T_VALUE x)   = f$ TR_VALUE x
collectAnds _ f _ (T_RESET)     = f$ TR_RESET

termToSMV :: Term -> (String,Set.Set String)
termToSMV t = propToSMV (translateTerm t)
