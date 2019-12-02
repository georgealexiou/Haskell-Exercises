-- comp2209 Functional Programming Challenges
-- (c) University of Southampton 2019
-- Skeleton code to be updated with your solutions
-- The dummy functions here simply return a randome value that is usually wrong 

-- DO NOT MODIFY THE FOLLOWING LINES OF CODE
module Challenges (alphaNorm, countAllReds, printLambda, parseLet, letToLambda,
    LamExpr(LamApp, LamAbs, LamVar), LetExpr(LetApp, LetDef, LetFun, LetVar, LetNum),
    lambdaToLet) where

-- Import standard library and parsing definitions from Hutton 2016, Chapter 13
import Data.Char
import Parsing

import qualified Data.Map
import qualified Data.List

-- abstract data type for simple lambda calculus expressions
data LamExpr = LamApp LamExpr LamExpr  |  LamAbs Int LamExpr  |  LamVar Int deriving (Show, Eq)

-- abstract data type for simple let expressions
data LetExpr = LetApp LetExpr LetExpr  |  LetDef [([Int], LetExpr)] LetExpr |  LetFun Int | LetVar Int | LetNum Int deriving (Show, Eq)
-- END OF CODE YOU MUST NOT MODIFY


-- ADD YOUR OWN CODE HERE

-------------------------------------------------------------------------------------------------------------
-- Challenge 1 ----------------------------------------------------------------------------------------------
-- generate the alpha normal form for a simple lambda calculus expression
-- each bound variable is chosen to be the first one possible
alphaNorm :: LamExpr -> LamExpr

type NameMap = Data.Map.Map Int Int

getFreeInstances :: LamExpr -> [Int]
getFreeInstances (LamVar x)           = [x]
getFreeInstances (LamAbs x e) = Data.List.delete x $ getFreeInstances e
getFreeInstances (LamApp l r) = Data.List.nub $ getFreeInstances l ++ getFreeInstances r

alphaNorm expr = ar freeVariables expr
  where freeVariables :: NameMap
        freeVariables = Data.Map.fromList [(x,x) | x <- getFreeInstances expr]

        ar :: NameMap -> LamExpr -> LamExpr
        ar names (LamVar x) = LamVar $ names Data.Map.! x
        ar names (LamApp l r) = LamApp (ar names l) (ar names r)
        ar names (LamAbs x e) =
          let freeVars  = Data.List.delete x $ getFreeInstances e
              usedNames = map (names Data.Map.!) freeVars
              newName   = head [n | n <- [0..], n `notElem` usedNames]
              newMap    = Data.Map.insert x newName names
          in  LamAbs newName $ ar newMap e

-------------------------------------------------------------------------------------------------------------
-- Challenge 2 ----------------------------------------------------------------------------------------------
-- count all reduction paths for a given lambda expression m, of length up to a given limit l
countAllReds :: LamExpr -> Int -> Int
countAllReds _ _ = -1


-------------------------------------------------------------------------------------------------------------
-- Challenge 3 ----------------------------------------------------------------------------------------------
-- pretty print a lambda expression, combining abstraction variables
-- also recognising Scott numerals and printing these as numbers
-- finalising omitting brackets where possible and safe to do so
printLambda :: LamExpr -> String
printLambda _ = ""


-------------------------------------------------------------------------------------------------------------
-- Challenge 4 ----------------------------------------------------------------------------------------------
-- parse recursive let expression, possibly containing numerals
parseLet :: String -> Maybe LetExpr
parseLet _ = Just (LetVar (-1))


-------------------------------------------------------------------------------------------------------------
-- Challenge 5 ----------------------------------------------------------------------------------------------
-- translate a let expression into lambda calculus, using Scott numerals
-- convert let symbols to lambda variables using Jansen's techniques rather than Y
letToLambda :: LetExpr -> LamExpr
letToLambda _ = LamVar (-1)


-------------------------------------------------------------------------------------------------------------
-- Challenge 6 ----------------------------------------------------------------------------------------------
-- convert a lambda calculus expression into one using let expressions and application
-- can use lambda lifting techniques described in wikipedia article
lambdaToLet :: LamExpr -> LetExpr
lambdaToLet _ = LetVar (-1)

{-
lambdaToLet (Var x)         = LamVar x
lambdaToLet (App e1 e2)     = LamApp (convertLet e1) (convertLet e2)
lambdaToLet (Let x e1 e2) | length x == 1 = LamApp (LamAbs (head x) (lambdaToLet e2)) (lambdaToLet e1)
                         | otherwise = LamApp (LamAbs (head x) (convertLet e2)) (absSequence (tail x) e1)
                         where
                           -- Generate a sequence of lambda abstractions
                           absSequence :: [Int] -> Expr -> LamExpr
                           absSequence x' e | length x' == 1 = LamAbs (head x') (lambdaToLet e)
                                            | otherwise = LamAbs (head x') (absSequence (tail x') e) 
-}
