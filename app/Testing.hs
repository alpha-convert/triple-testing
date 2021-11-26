module Testing where

import Test.QuickCheck.Gen
import Test.QuickCheck
import Control.Monad.Identity
import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import Syntax
import Semantics
import GHC.Base (undefined)
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Set as Set

data ConstrTyp = EqZ | GeqZ | GtZ | NeqZ

data GSAction = BoolSet Var Bool | ConcretizeNum Var | Constrain ConstrTyp NumExp
type GeneratorScript = [GSAction]

{-
To build GeneratorScripts:
1. Build the undirected dependency graph of vars in the Prop
2. Pick a random DAG-ification of the graph (https://stackoverflow.com/questions/8127932/how-to-convert-an-undirected-graph-to-a-dag)
3. Toposort the dag to get a list of concretizations
4. Maximally front-load the script: for every x, include all of the constraints e
   including x which only mention concretized variables immediately before x.
-}


minus :: NumExp -> NumExp -> NumExp
minus = NEBinOp NEMinus

{-data Prop = PropVar Var | RelExp PropRel NumExp NumExp | PBO PropBinOp Prop Prop | PMO PropMonOp Prop-}
baseScripts :: Prop -> [GeneratorScript]
baseScripts p = go (driveNegations p)
  where
    go (PropVar b) = [[BoolSet b True],[BoolSet b False]]
    go (PMO PNot (PropVar b)) = [[BoolSet b True],[BoolSet b False]]
    go (RelExp REq e1 e2) = [[Constrain EqZ (minus e1 e2)]]
    go (RelExp RNeq e1 e2) = [[Constrain NeqZ (minus e1 e2)]]
    go (RelExp RGeq e1 e2) = [[Constrain GeqZ (minus e1 e2)]]
    go (RelExp RLeq e1 e2) = [[Constrain GeqZ (minus e2 e1)]]
    go (RelExp RGt e1 e2) = [[Constrain GtZ (minus e1 e2)]]
    go (RelExp RLt e1 e2) = [[Constrain GtZ (minus e2 e1)]]
    go (PBO PAnd p1 p2) = (++) <$> go p1 <*> go p2
    go (PBO POr p1 p2) = go p1 ++ go p2
    go (PMO PNot _) = error "Impossible."

{- A script s is well-concretized if:
  for every concretization of a variable x,
  all constraints involving x before 
  involve concretized variables.
   -}
scripts :: Prop -> [GeneratorScript]
scripts = undefined


genIntVal :: Gen Val
genIntVal = VInt <$> choose intRange

genBoolVal :: Gen Val
genBoolVal = VBool <$> arbitrary

{-data Typ = TyUnit | TyInt | TyBool | TyArr Typ-}
genValOfTyp :: Typ -> Gen Val
genValOfTyp TyUnit = return VUnit
genValOfTyp TyInt = genIntVal
genValOfTyp TyBool = genBoolVal
genValOfTyp (TyArr t) = VArray . Seq.fromList <$> resize listLenSize (listOf (genValOfTyp t))

genStore :: Method -> Gen Store
genStore m = do
  vals <- mapM (genValOfTyp . snd) (args m)
  let argnames = map fst (args m)
  return $ Map.fromList $ zip argnames vals

intRange = (0,10)
listLenSize = 10


satProp :: Store -> Prop -> Bool
satProp s p =
  case runComp (evalProp p) s of
    Right (b,_) -> b
    Left _ -> error "Failed to do a thing"

satHoare :: Method -> Property
satHoare m =
  forAll (genStore m) (\sto ->
    let preProp = all (satProp sto) (pres m) in
    preProp ==>
    case runComp (runCmd (body m)) sto of
      Right (retVal,sto) ->
        let sto' = Map.insert (retName m) retVal sto in
        conjoin (map (satProp sto') (posts m))

  )
