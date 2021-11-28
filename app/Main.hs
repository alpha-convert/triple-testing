{-# LANGUAGE TupleSections #-}

module Main where

import Test.QuickCheck ( choose, frequency, generate, Gen, quickCheck, listOf )

import qualified Data.Sequence as Seq
import Parser ( method, parseFile, prop )
import Testing
import Bandit
import Data.List (intersperse, nub, sort)
import Control.Monad (replicateM)
import GenScript ( makeGeneratorScripts, interpScript )
import Text.Parsec (parse)
import Data.Maybe (isJust)
import Data.Foldable (toList)

import Data.IntervalSet hiding (null,toList)
import Data.Interval hiding (null)

{- For integers in the (-10,10) range, generate x,y, sat:
  0 <= x < y <= 5 -}

bad :: Gen (Int, Int)
bad = do
  x <- choose (-10,10)
  y <- choose (-10,10)
  return (x,y)

notGreat :: Gen (Int,Int)
notGreat = do
  x <- choose (0,10)
  y <- choose (-10,5)
  return (x,y)

baseline :: Gen (Int,Int)
baseline = do
  x <- choose (0,5)
  y <- choose (0,5)
  return (x,y)

conc1 :: Gen (Int,Int)
conc1 = do
  y <- choose (-10,10)
  x <- choose (0,y-1)
  return (x,y)


conc2 :: Gen (Int,Int)
conc2 = do
  x <- choose (0,10)
  y <- choose (x,5)
  return (x,y)

perfect :: Gen (Int,Int)
perfect = do
  x <- choose (0,4)
  y <- choose (x+1,5)
  return (x,y)


pred :: (Int,Int) -> Bool
pred (x,y) = 0 <= x && x < y && y <= 5

wp :: (Int,Int) -> Gen Bool
wp (x,y) = frequency [(x,return True),(y,return False)]

gen1 :: Gen (Maybe (Int,Int))
gen1 = do
  y <- choose (0,2)
  x <- choose (1,y)
  if y < 1 then return Nothing
  else return $ Just (x,y)

gen2 :: Gen (Maybe (Int,Int))
gen2 = do
  x <- choose (1,10)
  y <- choose (x,2)
  if x > 2 then return Nothing
  else return $ Just (x,y)

perfect2 :: Gen (Maybe (Int,Int))
perfect2 = do
  y <- choose (1,2)
  x <- choose (y,2)
  return $ Just (x,y)



main :: IO ()
main = do
  let n = 100
  let x = parse Parser.prop "" "0 <= y && x <= 100 && 50 <= x && x <= y"
  -- let x = parse Parser.prop "" "x <= y" 
  -- let x = parse Parser.prop "" "0 <= x && 0 <= y && x <= 2 && y <= 2 && x * y == 2"
  -- let x = parse Parser.prop "" "0 <= x && 0 <= y && x + y <= 100"
  let y = case x of Right z -> z
  h <- generate $ makeGeneratorScripts 100 y
  print h
  let gs = map GenScript.interpScript h
  vs <- generate $ take n <$> ucb1 isJust gs
  let zs = filter valid vs
  print (map val zs)
  let uniqs = nub $ map val zs
  print ("#unique:" ++ show (length uniqs))
  print ("Stats:" ++ (show $ toList $ stats $ last zs))
  {-m <- parseFile method "gcd.ttt"
  quickCheck (satHoare m)
  -}
  return ()