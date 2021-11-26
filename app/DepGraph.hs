{-# LANGUAGE TupleSections #-}

module DepGraph (genConcrOrder) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import GHC.IO (unsafePerformIO)
import Syntax
import Test.QuickCheck

type DepGraph = Map.Map Var (Set.Set Var)

unionGraph :: DepGraph -> DepGraph -> DepGraph
unionGraph = Map.unionWith Set.union

diagGraph :: Set.Set Var -> DepGraph
diagGraph s = Set.fold (\v g -> Map.insert v (Set.delete v s) g) Map.empty s

freeVars (NEVar x) = Set.singleton x
freeVars (NEInt _) = Set.empty
freeVars (NEBinOp _ e1 e2) = Set.union (freeVars e1) (freeVars e2)
freeVars (NEMonOp _ e) = freeVars e

depUGraph :: Prop -> DepGraph
depUGraph (PropVar _) = Map.empty
depUGraph (RelExp _ e1 e2) = diagGraph (Set.union (freeVars e1) (freeVars e2))
depUGraph (PBO _ p1 p2) = unionGraph (depUGraph p1) (depUGraph p2)
depUGraph (PMO _ p) = depUGraph p

{-
Orient edges as you do the DFS traversal,
pointing each undirected edge away from the vertex
that you're currently expanding.
(https://stackoverflow.com/questions/8127932/how-to-convert-an-undirected-graph-to-a-dag)
-}

removeEdges :: [(Var, Var)] -> DepGraph -> DepGraph
removeEdges [] g = g
removeEdges ((v, w) : vs) g = Map.update (Just . Set.delete w) v (removeEdges vs g)


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
genConcrOrder = randTopo . depUGraph