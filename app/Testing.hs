{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TupleSections #-}
module Testing where

import Test.QuickCheck.Gen
import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import Syntax
import Semantics
import GHC.Base (undefined)
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Set as Set
import GenScript
import GHC.IO (unsafePerformIO)
import Bandit (ucb1, Result (val))
import Data.Maybe (isJust, fromJust, catMaybes, mapMaybe)
import Data.List (nub, sort)


satProp :: Store -> Prop -> Bool
satProp s p =
  case runComp (evalProp p) s of
    Right (b,_) -> b
    Left _ -> error "Failed to do a thing"


satHoare :: Int -> Method -> IO ()
satHoare n m = do
  let numVars = length (args m)
  let numScripts :: Int = numVars * numVars
  !gScripts <- generate $ makeGeneratorScripts numScripts (foldr (PBO PAnd) (PropConst True) (pres m))
  putStrLn ("Found " ++ (show $ length gScripts) ++ " generator scripts while searching for " ++ show numScripts)
  let !gs = map GenScript.interpScript gScripts
  let bandit = map val <$> ucb1 isJust gs
  putStrLn ("Generating " ++ show n ++ " inputs")
  !cases <- Data.Maybe.catMaybes . take n <$> generate bandit
  let numDiscarded = n - length cases
  putStrLn ("Discarded: " ++ show numDiscarded)
  putStrLn ("Unique: " ++ show (length $ nub cases))
  let results = map (\sto -> (exampleSat m sto,sto)) cases
  let failures = mapMaybe (\(r,sto) -> if not r then Just sto else Nothing) results
  if not (null failures) then
    do
      putStrLn "Failed!"
      putStrLn $ "Counterexample: " ++ show (head failures)
  else
    putStrLn "All tests passed."
  return ()

exampleSat :: Method -> Store -> Bool
exampleSat m sto =
  case runComp (runCmd (body m)) sto of
      Right (retVal,sto) ->
        let sto' = Map.insert (retName m) retVal sto in
        all (satProp sto') (posts m)
      Left _ -> undefined
  {-forAll (genStore m) (\sto ->
    {- This check is really pro-forma since we're generatng
       well-spec'd stores... But if it ever fails, that
       signals that we've got a bug. -}
    let preProp = all (satProp sto) (pres m) in
    preProp ==>
    
  )
  -}
