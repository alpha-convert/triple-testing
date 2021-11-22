{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE NamedFieldPuns #-}

module Main where

import Test.QuickCheck ( choose, frequency, generate, Gen )

import Parser ( method, parseFile )
import Testing ( satHoare )
import Bandit
import Data.List (intersperse, nub, sort)
import Control.Monad (replicateM)

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

main :: IO ()
main = do
  let n = 1000
  vs <- generate $ take n <$> ucb1 Main.pred [bad,notGreat,baseline,conc1,conc2]
  let zs = nub $ sort $ map val $ filter valid vs
  print $ show $ length zs
  ws <- filter Main.pred <$> replicateM n (generate conc1)
  ks <- filter Main.pred <$> replicateM n (generate conc2)
  print $ show $ length $ nub $ sort ws
  print $ show $ length $ nub $ sort ks
  return ()
  {-m <- parseFile method "gcd.ttt"
  quickCheck (satHoare m)
  -}