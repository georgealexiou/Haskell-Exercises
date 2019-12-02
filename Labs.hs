{-# LANGUAGE DeriveGeneric #-}
--SKELETON FILE FOR COURSEWORK 1 for COMP2209, 2019
--CONTAINS ALL FUNCTIONS REQIURED FOR COMPILATION AGAINST THE TEST SUITE
--MODIFY THE FUNCTION DEFINITIONS WITH YOUR OWN SOLUTIONS
--IMPORTANT : DO NOT MODIFY ANY FUNCTION TYPES
--Julian Rathke, Oct 2019

module Exercises (histogram,approxSqrt,longestCommonSubsequence,neighbours,findBonding,insertFromCurrentNode,VTree(..),Direction(..),Trail(..),Zipper(..),Instruction(..),Stack,SMProg,evalInst,findMaxReducers,optimalPower) where

-- The following two imports are needed for testing, do not delete
import GHC.Generics (Generic,Generic1)
import Control.DeepSeq
import Data.List (foldl', zipWith4, sortBy)
import Data.Function (on)
import Data.Tuple

-------------------------------------------------------------------------------------------------------------
-- Exercise A1 ----------------------------------------------------------------------------------------------
histogram :: Int -> [Int] -> [Int]

histogram n xs
    | n <= 0 = error "Error: can't have n<=0"
    | xs == [] = []
    | otherwise = [(length . filter (==y)) [x `div` n | x <- xs] | y <- [0..(maximum(xs) `div` n)]]


-------------------------------------------------------------------------------------------------------------
-- Exercise A2 ----------------------------------------------------------------------------------------------
approxSqrt :: Double -> Double -> Double

approxSqrt d eps 
    | d <= 0 = error "Cannot compute square root of 0"
    | eps <= 0 = error "Cannot have negative number"
    | eps == sqrt d = 1
    | otherwise = approxSqrt' d eps 1

approxSqrt' d eps x
    | x == 0 = 1
    | ((x + d/x)/2) - (sqrt d) < eps = ((x + d/x)/2)
    | otherwise = approxSqrt' d eps ((x + d/x)/2)


-------------------------------------------------------------------------------------------------------------
-- Exercise A3 ----------------------------------------------------------------------------------------------
longestCommonSubsequence :: Eq a => [[a]] -> [a]
longestCommonSubsequence xss
    | xss == [] = []
    | length xss == 1 = head xss
    | [] `elem` xss = []

longestCommonSubsequence (x:y:xs) = longestCommonSubsequence (longestCommonSubsequence' x y : xs)

longestCommonSubsequence' :: Eq a => [a] -> [a] -> [a]
longestCommonSubsequence' [] _ = []
longestCommonSubsequence' _ [] = []
longestCommonSubsequence' (x:xs) (y:ys) | x == y    = x : longestCommonSubsequence' xs ys
                           | otherwise = longest (longestCommonSubsequence' (x:xs) ys) (longestCommonSubsequence' xs (y:ys))
                           where
                             longest a b | length a > length b = a
                                         | otherwise = b


-------------------------------------------------------------------------------------------------------------
-- Exercise A4 ----------------------------------------------------------------------------------------------
type Point a = (a,a)
type Metric a = (Point a) -> (Point a) -> Double

neighbours ::  Int -> Metric a -> Point a -> [Point a] -> [Point a]
neighbours k d p ps 
    | k < 0 = error "Negative k"
    | k == 0 = []
    | length ps == 0 = []
    | length ps < k = []

neight a b m = m

getManhattan (x1, y1) (x2, y2) = abs(x1 - x2) + abs(y1 - y2)


-------------------------------------------------------------------------------------------------------------
-- Exercise A5 ----------------------------------------------------------------------------------------------
findBonding :: Eq a => (a -> a -> Bool) -> [a] -> Maybe [(a,a)]
findBonding p xs
    | odd(length xs) = error "odd"
    | otherwise = Just (recursion ([ (x,y) | x <- xs, y <- xs, x/=y, p x y]))

recursion :: Eq a => [(a,a)] -> [(a,a)]
recursion xs
    | (swap(head xs)) `elem` xs  = recursion (filter (\x -> fst x /= a && fst x /= snd x && fst x /= b && snd x /= b) xs ++ [(a,b)])
    | otherwise = xs
        where (a,b) = head xs

makeSymmetrics :: Eq a => [(a,a)] -> [(a,a)]
makeSymmetrics xs = foldr (\t l -> t:(swap t):l) [] xs


-------------------------------------------------------------------------------------------------------------
-- Exercise A6 ----------------------------------------------------------------------------------------------
data VTree a = Leaf | Node (VTree a) a Int (VTree a) deriving (Eq,Show,Generic,Generic1)
data Direction a = L a Int (VTree a) | R a Int (VTree a) deriving (Eq,Show,Generic,Generic1)
type Trail a = [Direction a]
type Zipper a = (VTree a, Trail a)

instance NFData a => NFData (VTree a)
instance NFData a => NFData (Direction a)

insertFromCurrentNode :: Ord a => a -> Zipper a -> Zipper a
insertFromCurrentNode v z
    | z == (Leaf, []) = (Leaf, [])

mkTree :: Ord a => [a] -> Zipper a
mkTree = foldl (\z -> \x -> insertFromCurrentNode x z) (Leaf, [])


-------------------------------------------------------------------------------------------------------------
-- Exercise A7 ----------------------------------------------------------------------------------------------
data Instruction = Add | Mul | Dup | Pop deriving (Eq,Ord,Show,Generic)
type Stack = [Int]
type SMProg = [Instruction] 

instance NFData (Instruction)

evalInst :: Stack -> SMProg -> Stack
evalInst [] _ = error "Cannot have empty stack"
evalInst s [] = s
evalInst s p
    | (head p == Mul || head p == Add) && length s == 1 = error "Input Stack doesn't contain two elements! Cant Add or Mul:" ++ s
    | head p == Mul = evalInst ((head s * head(tail s)) : tail(tail s)) (tail p)
    | head p == Add = evalInst ((head s + head(tail s)) : tail(tail s)) (tail p)
    | head p == Dup = evalInst ((head s) : s) (tail p)
    | head p == Pop = evalInst (tail s) (tail p)


-------------------------------------------------------------------------------------------------------------
-- Exercise A8 ----------------------------------------------------------------------------------------------
findMaxReducers :: Stack -> [SMProg]
findMaxReducers ns
    | length ns == 0 = []
    | length ns == 1 = [[]]
    | otherwise = findMaxReducers' ns []

findMaxReducers' :: Stack -> [SMProg] -> [SMProg]
findMaxReducers' s [] = findMaxReducers' s ps
     where
        ps = [ [p] | p <- determineInst (head s) (head (tail s))]

findMaxReducers' s ps
    | length (evalInst s (head ps)) == 1 = ps
    | otherwise = findMaxReducers' s ps1
        where
            ps1 = [ p ++ [s] | p <- ps, s <- determineInst (head s1) (head(tail s1))]
            s1 = evalInst s (head ps)


determineInst :: Int -> Int -> SMProg
determineInst x y
    | x == 0 && y == 0 = [Add, Mul, Pop]
    | x == 0 = [Add, Pop]
    | x > 0 && y == 0 = [Add]
    | x == 1 || y == 1 = [Add]
    | x*y > 0 = [Mul]
    | x < 0 = [Pop]
    | x > 0 && y < 0 = [Pop]


-------------------------------------------------------------------------------------------------------------
-- Exercise A9 ----------------------------------------------------------------------------------------------
optimalPower :: Int -> SMProg
optimalPower n
    | n <= 0 = error "Cannot accept input that is 0 or smaller"
    | n == 1 = []
