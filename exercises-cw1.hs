{-# LANGUAGE DeriveGeneric #-}
--George Alexiiou

module Exercises (histogram,approxSqrt,longestCommonSubsequence,neighbours,findBonding,insertFromCurrentNode,VTree(..),Direction(..),Trail(..),Zipper(..)) where

-- The following two imports are needed for testing, do not delete
import GHC.Generics (Generic,Generic1)
import Control.DeepSeq


-- Exercise A1
histogram :: Int -> [Int] -> [Int]

histogram n xs
    | n <= 0 = error "Error: can't have n<=0"
    | xs == [] = []
    | otherwise = [(length . filter (==y)) [x `div` n | x <- xs] | y <- [0..(maximum(xs) `div` n)]]

-- Exercise A2
approxSqrt :: Double -> Double -> Double
approxSqrt d eps = -1

-- Exercise A3
longestCommonSubsequence :: Eq a => [[a]] -> [a]
longestCommonSubsequence xss = []

-- Exercise A4
type Point a = (a,a)
type Metric a = (Point a) -> (Point a) -> Double

neighbours ::  Int -> Metric a -> Point a -> [Point a] -> [Point a]
neighbours k d p ps = []

-- Exercise A5
findBonding :: Eq a => (a -> a -> Bool) -> [a] -> Maybe [(a,a)]
findBonding p xs = Nothing

-- Exercise A6

data VTree a = Leaf | Node (VTree a) a Int (VTree a) deriving (Eq,Show,Generic,Generic1)
data Direction a = L a Int (VTree a) | R a Int (VTree a) deriving (Eq,Show,Generic,Generic1)
type Trail a = [Direction a]
type Zipper a = (VTree a, Trail a)

instance NFData a => NFData (VTree a)
instance NFData a => NFData (Direction a)

insertFromCurrentNode :: Ord a => a -> Zipper a -> Zipper a
insertFromCurrentNode v z = (Leaf,[])


-- Exercise A7
-- Exercise A8
-- Exercise A9
-- Exercise A10