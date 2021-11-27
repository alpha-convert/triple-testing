{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module GenScript where

import qualified Data.Map as Map
import qualified Data.Set as Set
import GHC.IO (unsafePerformIO)
import Syntax
import Test.QuickCheck
import Control.Monad
import Data.List (nub)

type DepGraph = Map.Map Var (Set.Set Var)

unionGraph :: DepGraph -> DepGraph -> DepGraph
unionGraph = Map.unionWith Set.union

diagGraph :: Set.Set Var -> DepGraph
diagGraph s = Set.fold (\v g -> Map.insert v (Set.delete v s) g) Map.empty s


depUGraph :: Prop -> DepGraph
{-depUGraph (PropVar _) = Map.empty-}
depUGraph (RelExp _ e1 e2) = diagGraph (Set.union (freeNumVar e1) (freeNumVar e2))
depUGraph (PBO _ p1 p2) = unionGraph (depUGraph p1) (depUGraph p2)
depUGraph (PMO _ p) = depUGraph p

{-
(https://stackoverflow.com/questions/8127932/how-to-convert-an-undirected-graph-to-a-dag)
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
data GSAction = Concretize Var | Constrain Constraint deriving (Eq,Ord)
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
  show (Constrain c) = show c

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
    go _ = fail "impossible"
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

singleVarConstr :: Constraint -> Bool
singleVarConstr (C _ e) = Set.size (Syntax.freeNumVar e) == 1

constructScript :: Set.Set Constraint -> [Var] -> GeneratorScript
constructScript cs vs = let svcs = Set.filter singleVarConstr cs in
  (Constrain <$> Set.toList svcs) ++ go (cs Set.\\ svcs) vs []
  where
    go cs [] concrd = []
    go cs (v:vs) concrd =
      let v_constrs = Set.filter (concreteWRT concrd v) cs in
      fmap Constrain (Set.toList v_constrs) ++ Concretize v : go (cs Set.\\ v_constrs) vs (v:concrd)


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