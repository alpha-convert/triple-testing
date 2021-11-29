{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module GenScript (makeGeneratorScripts, interpScript) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import GHC.IO (unsafePerformIO)
import Syntax
    ( driveNegations,
      freeNumVar,
      NumExp(..),
      NumExpBinOp(NEMinus),
      Prop(..),
      PropBinOp(POr, PAnd),
      PropRel(RLt, REq, RNeq, RGeq, RLeq, RGt),
      Var )
import Test.QuickCheck ( elements, shuffle, Gen, choose )
import Control.Monad ( replicateM )
import Data.List (nub)
import Control.Monad.State
import Data.IntervalSet hiding (null)
import Data.Interval hiding (null)
import qualified Semantics
import Control.Monad.Random (Random)
import qualified Debug.Trace as Debug
import Data.Maybe (fromJust)

type DepGraph = Map.Map Var (Set.Set Var)

unionGraph :: DepGraph -> DepGraph -> DepGraph
unionGraph = Map.unionWith Set.union

diagGraph :: Set.Set Var -> DepGraph
diagGraph s = Set.fold (\v g -> Map.insert v (Set.delete v s) g) Map.empty s


depUGraph :: Prop -> DepGraph
{-depUGraph (PropVar _) = Map.empty-}
depUGraph (PropConst _) = Map.empty
depUGraph (RelExp _ e1 e2) = diagGraph (Set.union (freeNumVar e1) (freeNumVar e2))
depUGraph (PBO _ p1 p2) = unionGraph (depUGraph p1) (depUGraph p2)
depUGraph (PMO _ p) = depUGraph p

{-
(https://stackoverflow.com/questions/8127932/how-to-convert-an-undirected-graph-to-a-dag)
-}

{-
should really deterministically break into CCs,
and then to random toposort on each CC: this decreases
the possibilities by a factor of
-}
randTopo :: DepGraph -> Gen [Var]
randTopo g = do
  vs <- shuffle (Map.keys g) {- this should work for doing CCs... -}
  dfsLoop vs [] Set.empty
  where
    dfsLoop [] ord visited = return ord
    dfsLoop (v : stack) ord visited =
      if Set.member v visited
      then dfsLoop stack ord visited
      else
        let ord' = v : ord in
        let visited' = Set.insert v visited in
        let neighbors = Map.lookup v g in
            case neighbors of
              Nothing -> dfsLoop stack ord visited'
              Just ns -> do
                let nsList = filter (not . flip Set.member visited) (Set.toList ns)
                ns' <- (++ stack) <$> shuffle nsList
                dfsLoop ns' ord' visited'


genConcrOrder :: Prop -> Gen [Var]
genConcrOrder p = let !g = depUGraph p in
                  randTopo g

data ConstrTyp = EqZ | GeqZ | GtZ | NeqZ deriving (Eq,Ord)
data Constraint = C ConstrTyp NumExp deriving (Eq,Ord)
data GSAction = Concretize Var | Constrain (Maybe Var) Constraint deriving (Eq,Ord)
                               {- Variable which is being constrained -}
type GeneratorScript = [GSAction]

instance Show ConstrTyp where
  show EqZ = "== 0"
  show GeqZ = ">= 0"
  show GtZ = "> 0"
  show NeqZ = "!= 0"
instance Show Constraint where
  show (C c e) = show e ++ show c
instance Show GSAction where
  show (Concretize x) = "!" ++ x
  show (Constrain v c) = "{" ++ show v ++ "} " ++ show c

varsMentioned :: GeneratorScript -> Set.Set Var
varsMentioned [] = Set.empty
varsMentioned (Concretize x:s) = Set.insert x (varsMentioned s)
varsMentioned (Constrain Nothing (C _ e) : s) = Set.union (Syntax.freeNumVar e) (varsMentioned s)
varsMentioned (Constrain (Just x) (C _ e) : s) = Set.insert x $ Set.union (Syntax.freeNumVar e) (varsMentioned s)


{-
To build GeneratorScripts:
1. Build the undirected dependency graph of vars in the Prop
2. Pick a random DAG-ification of the graph (https://stackoverflow.com/questions/8127932/how-to-convert-an-undirected-graph-to-a-dag)
3. Toposort the dag to get a list of concretizations
4. Maximally front-load the script: for every x, include all of the constraints e
   including x which only mention concretized variables immediately before x.
-}

constraints :: Prop -> [Set.Set Constraint]
constraints = go . driveNegations
  where
    go :: Prop -> [Set.Set Constraint]
    go (RelExp REq e1 e2) = [Set.singleton $ C EqZ (minus e1 e2)]
    go (RelExp RNeq e1 e2) = [Set.singleton $ C NeqZ (minus e1 e2)]
    go (RelExp RGeq e1 e2) = [Set.singleton $ C GeqZ (minus e1 e2)]
    go (RelExp RLeq e1 e2) = [Set.singleton $ C GeqZ (minus e2 e1)]
    go (RelExp RGt e1 e2) = [Set.singleton $ C GtZ (minus e1 e2)]
    go (RelExp RLt e1 e2) = [Set.singleton $ C GtZ (minus e2 e1)]
    go (PBO PAnd p1 p2) = Set.union <$> go p1 <*> go p2
    go (PBO POr p1 p2) = do
      cs1 <- go p1
      cs2 <- go p2
      [cs1,cs2]
    go _ = [Set.empty]
    minus = NEBinOp NEMinus


{- constraint is concrete with respect to concretized variables vs,
   includes no uncocreteized (other varaibles), and includes variable of import var. -}
{- data NumExp = NEVar Var | NEInt Int | NEBinOp NumExpBinOp NumExp NumExp | NEMonOp NumExpMonOp NumExp deriving (Eq,Ord,Show)-}
concreteWRT :: [Var] -> Var -> Constraint -> Bool
concreteWRT vs w (C _ e) = go vs w e
  where
    go vs w (NEVar x) = x == w || (x `elem` vs) {- Is this right? -}
    go vs w (NEInt _) = True
    go vs w (NEBinOp _ e1 e2) = go vs w e1 && go vs w e2
    go vs w (NEMonOp _ e) = go vs w e

singleVarConstr :: Constraint -> Maybe Var
singleVarConstr (C _ e) = if Set.size fvs == 1
                          then Just (Set.findMax fvs)
                          else Nothing
  where fvs = Syntax.freeNumVar e

filterMapFlip :: (a -> Maybe b) -> [a] -> [(b,a)]
filterMapFlip f [] = []
filterMapFlip f (x:xs) = case f x of
                           Nothing -> filterMapFlip f xs
                           Just y -> (y,x) : filterMapFlip f xs

constructScript :: Set.Set Constraint -> [Var] -> GeneratorScript
constructScript cs vs = let svcs = filterMapFlip singleVarConstr (Set.toList cs) in
  let (cs_left,body) = go (cs Set.\\ Set.fromList (map snd svcs)) vs [] in
  map (\(x,c) -> Constrain (Just x) c) svcs ++ body ++ (fmap (Constrain Nothing)) (Set.toList cs_left)
  where
    go cs [] concrd = (cs,[])
    go cs (v:vs) concrd =
      let v_constrs = Set.filter (concreteWRT concrd v) cs in
      let (cs_left,s') = go (cs Set.\\ v_constrs) vs (v:concrd) in
      (cs_left, fmap (Constrain (Just v)) (Set.toList v_constrs) ++ Concretize v : s')


{- Int parameter controls number of desired generators. We filter out
   duplicates. Assuming (strong) that there are K possible
   concr orders for p, and `genConcrOrder p` gives the uniform distribution,
   the probability that `makeGeneratorScripts n p` is missing a generator is:

   X_i = I[generator i is missing after n runs]
   P[exists i. X_i] <= KP[X_1]    -- (union bound)
                    == K(1-1/K)^n
                    <= Ke^(-n/K)  -- (1-x <= e^(-x))

  To get this to happen with prob eps, need n >= Klog(K/eps)
-}
makeGeneratorScripts :: Int -> Prop -> Gen [GeneratorScript]
makeGeneratorScripts n p =
  let !cs = constraints p in
  let (!concrOrders) :: Gen [Var] = genConcrOrder p in
  do
    {- We should check for satisfiability and filter out unsat constr sets. -}
    constrSets <- replicateM n $ elements cs
    genScripts <- mapM (\cset -> fmap (constructScript cset) concrOrders) constrSets
    return $ nub genScripts

data ScriptState = S {concrVars :: Map.Map Var Int, constrs :: Map.Map Var [Constraint]}

type Interp a = State ScriptState a

getConcrVar :: Var -> Interp Int
getConcrVar x = do
  st <- get
  let cvs = concrVars st
  return $ fromJust $ Map.lookup x cvs

partialEval :: Var -> NumExp -> Interp (Int -> Int)
partialEval x = go
  where
    go (NEVar y) = if x == y then return id
                   else const <$> getConcrVar y
    go (NEInt n) = return $ const n
    go (NEBinOp b e1 e2) = do
      let r = Semantics.evalNEBinOp b
      f <- go e1
      g <- go e2
      return $ \v -> r (f v) (g v)
    go (NEMonOp o e) = do
      let r = Semantics.evalNEMonOp o
      f <- go e
      return $ \v -> r (f v)

interpConstr :: Var -> Constraint -> Interp (IntervalSet Int)
interpConstr x (C r e) =
  do
    f <- partialEval x e
    let b = f 0
    let a = f 1 - b
    -- let !_ = Debug.trace ("While interpreting constraint " ++ (show (C r e)) ++ ", Got " ++ show e ++ " == " ++ show a ++ "*" ++ show x ++ "+" ++ show b) ()
    let isConstant = a == 0
    let root = -fromIntegral b / (fromIntegral a)
    case r of
      EqZ -> if a == 0 && b == 0
             then return Data.IntervalSet.whole
             else if a == 0 || (b `mod` a) /= 0
             then return Data.IntervalSet.empty
             else return (Data.IntervalSet.singleton $ Data.Interval.singleton (-b `div` a))
      {- ax+b >= 0 <=> x >= ceil(-b/a)-}
      GeqZ -> if isConstant then (if b >= 0 then return Data.IntervalSet.whole else return Data.IntervalSet.empty)
              else
                if a > 0 then
                  return $ Data.IntervalSet.singleton ((Finite $ ceiling root) <=..< PosInf)
                else
                  return $ Data.IntervalSet.singleton (NegInf <..<= (Finite $ floor root))
      GtZ -> if isConstant then (if b > 0 then return Data.IntervalSet.whole else return Data.IntervalSet.empty)
             else
               if a > 0 then
                 return $ Data.IntervalSet.singleton ((Finite $ ceiling root) <..< PosInf)
               else
                 return $ Data.IntervalSet.singleton (NegInf <..< (Finite $ floor root))
      {- ax+b != 0 <=> x != -b/a -}
      NeqZ -> if isConstant then (if b /= 0 then return Data.IntervalSet.whole else return Data.IntervalSet.empty)
              else return $ Data.IntervalSet.difference Data.IntervalSet.whole (Data.IntervalSet.singleton $ Data.Interval.singleton (-b `div` a))

sampleIntSet :: (Random a,Ord a) => (a,a) -> IntervalSet a -> Gen (Maybe a)
sampleIntSet (a,b) s =
  let s' = Data.IntervalSet.intersection s (Data.IntervalSet.singleton $ Finite a <=..<= Finite b) in
  let ints = toList s' in
  if null ints then return Nothing
  else do
    i <- elements ints
    let Finite x = Data.Interval.lowerBound i
    let Finite y = Data.Interval.upperBound i
    Just <$> choose (x,y)

interpConstrsFor :: Var -> Interp (IntervalSet Int)
interpConstrsFor x = do
  st <- get
  let csMap = constrs st
  let cs = fromJust $ Map.lookup x csMap
  Data.IntervalSet.intersections <$> mapM (interpConstr x) cs

{- I got lost in my monad stack so this is manual... -}
interpScript' :: ScriptState -> GeneratorScript -> Gen (Maybe (Map.Map Var Int))
interpScript' st [] = return (Just $ concrVars st)
interpScript' st ((Concretize x):script) = do
  let (s,st') = runState (interpConstrsFor x) st
  let cs = Map.lookup x (constrs st)
  -- let !_ = Debug.trace ("Concretizing variable " ++ x ++ " under constraint set" ++ (show s) ++ "\n" ++ "Derived from constraints: " ++ (show cs)) ()
  vX <- sampleIntSet (-10000,100000) s
  case vX of
    Nothing -> return Nothing
    Just n -> do
      -- let !_ = Debug.trace ("Variable " ++ x ++ " concretized to value " ++ show n) ()
      let cvs = concrVars st'
      let cvs' = Map.insert x n cvs
      let st'' = st' {concrVars = cvs'}
      interpScript' st'' script
interpScript' st ((Constrain (Just x) c):script) = do
  let cMap = constrs st
  let cMap' = Map.update (Just . (c:)) x cMap
  let st' = st {constrs = cMap'}
  interpScript' st' script
interpScript' st ((Constrain Nothing c):script) = do
  {-FXME!!!-}
  interpScript' st script

initState :: [Var] -> ScriptState
initState vars = S {concrVars = Map.empty, constrs= init}
  where
    init = foldr (`Map.insert` []) Map.empty vars

interpScript :: GeneratorScript -> Gen (Maybe Semantics.Store)
interpScript scr =
  let vars = Set.toList $ varsMentioned scr in
    do
      mp <- interpScript' (initState vars) scr
      return $ Map.map Semantics.VInt <$> mp
