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
approxSqrt d eps | d <= 0 = error "Cannot compute square root of 0"
                 | eps <= 0 = error "Cannot have negative number"
                 | otherwise = approxSqrt1 d eps 1

approxSqrt1 d eps x | (x + d/x)/2 - sqrt(d) < eps  = (x + d/x)/2
                    | otherwise = approxSqrt1 d eps (x+1)

--Exceptional Cases:
-- 25 5
-- 25 3
-- (12345^2) 1

-- Exercise A3
longestCommonSubsequence :: Eq a => [[a]] -> [a]
longestCommonSubsequence xss
    | xss == [] = []
    | length xss == 1 = head xss
    | [] `elem` xss = []

longestCommonSubsequence (x:y:xs) = longestCommonSubsequence (longestCommonSubsequence' x y : xs)

longestCommonSubsequence' :: Eq a => [a] -> [a] -> [a]
longestCommonSubsequence' (x:xs) (y:ys) | x == y    = x : longestCommonSubsequence' xs ys
                           | otherwise = longest (longestCommonSubsequence' (x:xs) ys) (longestCommonSubsequence' xs (y:ys))
                           where
                             longest a b | length a > length b = a
                                         | otherwise = b


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
data Instruction = Add | Mul | Dup | Pop deriving (Eq,Ord,Show,Generic)
type Stack = [Int]
type SMProg = [Instruction] 

instance NFData (Instruction)

evalInst :: Stack -> SMProg -> Stack
evalInst s p = []


-- Exercise A8
findMaxReducers :: Stack -> [SMProg]
findMaxReducers ns = []


-- Exercise A9
optimalPower :: Int -> SMProg
optimalPower n = []
