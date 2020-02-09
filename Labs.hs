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
import Data.List
import Data.List (foldl', zipWith4, sortBy)
import Data.Function (on)
import Data.Tuple

-------------------------------------------------------------------------------------------------------------
-- Exercise A1 ----------------------------------------------------------------------------------------------
histogram :: Int -> [Int] -> [Int]

histogram n xs
    | xs == [] = []
    | n <= 0 = error "Can't compute histogram for negative n"
    | otherwise = [(length . filter (==m)) [x `div` n | x <- xs] | m <- [0..(maximum(xs) `div` n)]]


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
longestCommonSubsequence' (x:xs) (y:ys) 
    | x == y = x : longestCommonSubsequence' xs ys
    | otherwise = longest (longestCommonSubsequence' (x:xs) ys) (longestCommonSubsequence' xs (y:ys))
        where
             longest a b | length a > length b = a
                         | otherwise = b


-------------------------------------------------------------------------------------------------------------
-- Exercise A4 ----------------------------------------------------------------------------------------------
type Point a = (a,a)
type Metric a = (Point a) -> (Point a) -> Double

neighbours :: Int -> Metric a -> Point a -> [Point a] -> [Point a]
neighbours k d p xs | k >= 0 = take k (sortBy (\x y -> compare (d p x) (d p y)) xs) 
                    | otherwise = error "Cannot have negative k"


-------------------------------------------------------------------------------------------------------------
-- Exercise A5 ----------------------------------------------------------------------------------------------

findBonding :: Eq a => (a -> a -> Bool) -> [a] -> Maybe [(a,a)]
findBonding p xs
    | length xs == 0 = error "Can't have empty list"
    | odd (length xs) = error "Can't have list of odd length"
    | otherwise = Just (makeSymmetrics (head (combos p xs)))


makeSymmetrics :: Eq a => [(a,a)] -> [(a,a)]
makeSymmetrics xs = foldr (\t l -> t:(swap t):l) [] xs

combos p xs = [ es | (e:es) <- mapM (const [ (x,y) | x <- xs, y <- xs, x/=y, p x y]) [1..getOdd xs], e `notElem` es]

getOdd xs
    | ((length xs) `div` 2) `mod` 2 == 1 = ((length xs) `div` 2)
    | otherwise = ((length xs) `div` 2) + 1


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
    | otherwise = map (\i -> if i==Add then Mul; else i) (findOptimal n (getEven n)) 
            
getEven n
    | (floor (2 * (logBase 2 (fromIntegral n)))) `mod` 2 == 0 = (floor (2 * (logBase 2 (fromIntegral n))))
    | otherwise = (floor (2 * (logBase 2 (fromIntegral n)))) + 1


findOptimal :: Int -> Int -> SMProg
findOptimal n d
    | length opt > 0 = head opt
    | otherwise = findOptimal n (d+2)
          where
             opt = take 1 [ p | p <- (generate d), findPower [1] p == [n]]

findPower :: Stack -> SMProg -> Stack
findPower [] _ = error "Cannot have empty stack"
findPower s [] = s
findPower s p
    | (head p == Mul || head p == Add) && length s == 1 = findPower [0] []
    | head p == Mul = findPower ((head s * head(tail s)) : tail(tail s)) (tail p)
    | head p == Add = findPower ((head s + head(tail s)) : tail(tail s)) (tail p)
    | head p == Dup = findPower ((head s) : s) (tail p)
    | head p == Pop = findPower (tail s) (tail p)


generate :: Int -> [SMProg]
generate i = [x| x <- mapM (const [Dup, Add]) [1..i], head x == Dup, last x == Add, ((length . filter (== Add)) x) == ((length . filter (== Dup)) x)]






