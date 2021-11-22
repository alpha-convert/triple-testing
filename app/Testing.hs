module Testing where

import Test.QuickCheck.Gen
import Test.QuickCheck
import Control.Monad.Identity
import Syntax
import qualified Data.Map as Map
import Semantics
import qualified Data.Sequence as Seq


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
