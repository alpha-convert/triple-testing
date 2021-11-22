{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
module Bandit where
import Test.QuickCheck.Gen
import qualified Data.Sequence as Seq
import GHC.Float (sqrtDouble)
import Data.Foldable (toList, maximumBy)
import GHC.IO (unsafePerformIO)
import qualified Debug.Trace as Debug
import GHC.Float.RealFracMethods (roundDoubleInt)

data Result a = R {val :: a, valid :: Bool, generator_idx :: Int, stats :: Seq.Seq (Double,Double), random :: Bool} deriving Show

epGreedy :: Double -> (a -> Bool) -> [Gen a] -> Gen [Result a]
epGreedy eps p gens = go stats
  where
      reward x = if p x then 1.0 else 0.0
      randomGen = do
          i <- choose (0,length gens - 1)
          let _ = Debug.trace ("Picked random number: " ++ show i) ()
          v <- gens !! i
          return (v,i)
      bestGen stats = do
          let avgs = map (uncurry (/)) $ toList stats
          i <- argmax id avgs
          let _ = Debug.trace ("Picked best avg at index: " ++ show i)
          v <- gens !! i
          return (v,i)
      stats = Seq.fromList $ map (const (0.0,1.0)) gens
      go stats = do
          r <- choose (0.0,1.0)
          (v, i) <- (if r < eps then randomGen else bestGen stats)
          let rwd_i = reward v
          let stats' = Seq.adjust (\(amt,num) -> (amt+rwd_i,num+1.0)) i stats
          let res = R {val=v,valid = rwd_i > 0.0,generator_idx=i,stats=stats',random= if r < eps then True else False}
          vs <- go stats'
          return $ res:vs

ucb1 :: (a -> Bool) -> [Gen a] -> Gen [Result a]
ucb1 p gens = do
    totRewards <- Seq.fromList . map reward <$> sequence gens
    let numRuns = Seq.fromList $ map (const (1.0 :: Double)) gens
    let stats = Seq.zip totRewards numRuns
    go 0 stats
  where
    reward x = if p x then 1.0 else 0.0 :: Double
    score n (rwd_j,n_j) = (rwd_j/n_j) + sqrtDouble (2 * log (fromIntegral n) / n_j)
    go (n :: Int) (stats :: Seq.Seq (Double,Double)) = do
        i <- argmax (score n) (toList stats)
        v <- gens !! i
        let rwd_i = reward v
        let stats' = Seq.adjust (\(amt,num) -> (amt+rwd_i,num+1.0)) i stats
        let r = R {val=v,valid = rwd_i > 0.0,generator_idx=i,stats=stats',random=False}
        vs <- go (n + 1) stats'
        return $ r:vs

argmax :: Ord b => (a -> b) -> [a] -> Gen Int
argmax f [] = error "Argmax given empty list"
argmax f (x:xs) = frequency $ (1,) . return <$> go 1 [0] (f x) xs
  where
      {- list of maximizing values -}
      go n ns _ [] = ns
      go n ns x (y:ys)
        | x > f y = go (n+1) ns x ys
        | x == f y = go (n+1) (n:ns) x ys
        | otherwise = go (n+1) [n] (f y) ys