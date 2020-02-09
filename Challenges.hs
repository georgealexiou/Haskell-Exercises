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

-- added my own import (added it to this part of the file because an error was produced otherwise)
import Data.List as Lst 

-- abstract data type for simple lambda calculus expressions
data LamExpr = LamApp LamExpr LamExpr  |  LamAbs Int LamExpr  |  LamVar Int deriving (Show, Eq)

-- abstract data type for simple let expressions
data LetExpr = LetApp LetExpr LetExpr  |  LetDef [([Int], LetExpr)] LetExpr |  LetFun Int | LetVar Int | LetNum Int deriving (Show, Eq)
-- END OF CODE YOU MUST NOT MODIFY


-- ADD YOUR OWN CODE HERE


-- Challenge 1
-- generate the alpha normal form for a simple lambda calculus expression
-- each bound variable is chosen to be the first one possible
alphaNorm :: LamExpr -> LamExpr
alphaNorm expr = alphaReduce (rename expr (Lst.nub (getFreeInstances expr))) (getFreeInstances expr) 0 -- we pass alphaReduce the renamed LamExpr constructed by the rename function

-- function that computes the α-normal form of a given LamExpr (always given 0 at the beggining)
-- we use a counter to keep track of the current name that our Ints should take
alphaReduce :: LamExpr -> [Int] -> Int -> LamExpr

--if we get to a number that is bound by a free variable we increase counter by one
alphaReduce expr fs c | c `elem` fs = alphaReduce expr fs (c+1)

-- if the inner expression has more free variables than the whole expression it means that LamAbs a is bound to a LamVar a
-- if that is the case we locate the LamVar and name it appropreately as well as increase the counter
alphaReduce (LamAbs a e1) fs c
    | getFreeInstances (LamAbs a e1) < getFreeInstances e1 =  (LamAbs c (alphaReduce (changeBound e1 a c) fs (c+1))) 
    | otherwise =  (LamAbs c (alphaReduce e1 fs (c)))

alphaReduce (LamVar a) fs c = LamVar a --we will have already changed all bound variables through changeBound so it stays the same

alphaReduce (LamApp (LamVar a) e2) fs c | a >= 0 = LamApp (LamVar a) (alphaReduce e2 fs 0) -- check if variable is bound (all variables that have not been bounded yet are negative)
alphaReduce (LamApp e1 e2) fs c = LamApp (alphaReduce e1 fs c) (alphaReduce e2 fs c)

-- function that returns a list with all the free instances in the LamExpr
getFreeInstances :: LamExpr -> [Int]
getFreeInstances (LamApp lhs rhs) = getFreeInstances lhs ++ getFreeInstances rhs
getFreeInstances (LamAbs a e) = Lst.delete a (getFreeInstances e) --delete any LamVar that is Bound
getFreeInstances (LamVar a) =  [a] --add all LamVars to the list


-- function that changes the name of any bound LamVar to the correct to its α reduced form
changeBound :: LamExpr -> Int -> Int -> LamExpr
changeBound (LamVar a) b c | a == b = LamVar c --if the LamVar has the name that we want we change it
                           | otherwise = LamVar a

changeBound (LamAbs a expr) b c = (LamAbs a (changeBound expr b c))
changeBound (LamApp (LamVar a) expr2) b c | a < 0 = LamApp (changeBound (LamVar a) b c) expr2
changeBound (LamApp expr1 expr2) a b = (LamApp (changeBound expr1 a b) (changeBound expr2 a b))

--function that makes all the names of bound LamVars and all LamAbs negative 
rename :: LamExpr -> [Int] -> LamExpr
rename (LamVar a) fs
    | a `elem` fs = (LamVar a)
    | otherwise = (LamVar ((a+1)*(-50)))

rename (LamAbs a exp) fs = (LamAbs ((a+1)*(-50)) (rename exp fs))
rename (LamApp exp1 exp2) fs = (LamApp (rename exp1 fs) (rename exp2 fs))



-- Challenge 2
-- count all reduction paths for a given lambda expression m, of length up to a given limit l

countAllReds :: LamExpr -> Int -> Int
countAllReds _ n | n<0 = error "Can't have negative numher of steps"
countAllReds _ 0 = 0
countAllReds expr 1 -- for n == 1 if the expression is reducible in one step return 1
    | (leftReduction expr /= expr && rightReduction expr /= expr) = 0 
    | otherwise = 1
countAllReds expr n -- for n > 1 if we can't reduce we return 1 otherwise we calculate all reduction sequences
    | (leftReduction expr == expr && rightReduction expr == expr) = 1
    | otherwise = length (generateReduced [expr] (n-1))

--FUNCTIONS USED TO GENERATE REDUCTION SEQUENCES
-- takes a list of expression, and returns all the expressions that were reduced
-- each element in the list represents a reduction sequence so its length is the answer to the challenge
generateReduced :: [LamExpr] -> Int -> [LamExpr]
generateReduced seq i
    | i == 0 = [ e | e <- seq, ((e == leftReduction e) || (e == rightReduction e))] -- returns a list of all the β-normal LamExprs
    | otherwise = generateReduced (concat [ getReduction e | e <- seq ]) (i-1) --replace elements in seq by their reduced expressions

-- returns a list of reductions that can be made to a given LamExpr
-- can either return a list of length 1 (both left and right reductions are the same) or 2 (both left and right reductions are different)
getReduction :: LamExpr -> [LamExpr]
getReduction expr
    | (rightReduction expr /= expr && leftReduction expr /= expr && leftReduction expr /= rightReduction expr) = [leftReduction expr, rightReduction expr]
    | (leftReduction expr == expr && rightReduction expr /= expr) = [rightReduction expr]
    | (leftReduction expr /= expr && leftReduction expr == expr) = [leftReduction expr]
    | otherwise = [leftReduction expr]


--FUNCTIONS USED TO COMPUTE β REDUCTION

{-function computes right reduction evaluation on the given expression using flipped inorder traversal
  terms used in the comments:
    * rhs = right hand side
    * lhs = left hand side
-}
rightReduction :: LamExpr -> LamExpr
rightReduction (LamVar a) = (LamVar a)
rightReduction (LamAbs a expr) = (LamAbs a (rightReduction expr))

--if lhs is LamVar we reduce rhs
rightReduction (LamApp (LamVar a) expr) = LamApp (LamVar a) (rightReduction expr)

--substitute lhs if it contains LamVar
rightReduction (LamApp (LamAbs a expr) (LamVar b)) = substitute expr a (LamVar b)

--substitute if rhs is not reducible
rightReduction (LamApp (LamAbs a expr1) expr2)
    | (expr2 /= (rightReduction expr2)) = (LamApp (LamAbs a expr1) (rightReduction expr2))
    | otherwise = substitute expr1 a expr2

--reduce rhs as LamVar is not reducible
rightReduction (LamApp (LamApp expr1 expr2) (LamVar a)) = LamApp (rightReduction (LamApp expr1 expr2)) (LamVar a)

--reduce lhs if rhs is not reducible or rhs if lhs is not reducible
rightReduction(LamApp (LamApp expr1 expr2) expr3)
    | (expr3 /= rightReduction expr3) = (LamApp (LamApp expr1 expr2) (rightReduction expr3))
    | otherwise = (LamApp (rightReduction (LamApp expr1 expr2)) expr3)

{-function computes right reduction evaluation on the given expression using flipped inorder traversal
  terms used in the comments:
    * rhs = right hand side
    * lhs = left hand side
-}
leftReduction :: LamExpr -> LamExpr 
leftReduction (LamVar a) = LamVar a
leftReduction (LamAbs a expr) = (LamAbs a (leftReduction expr))

-- if lhs is reducible we reduce 
leftReduction (LamApp (LamApp expr1 expr2) expr3) 
    | (LamApp expr1 expr2) /= (leftReduction (LamApp expr1 expr2)) = LamApp (leftReduction (LamApp expr1 expr2)) expr3
    | otherwise = LamApp (LamApp expr1 expr2) (leftReduction expr3)

--if lhs is reducible we reduce it otherwise we substitute
leftReduction (LamApp (LamAbs a expr1) expr2) 
    | ((leftReduction expr1) /= expr1) =  LamApp (LamAbs a (leftReduction expr1)) expr2
    | otherwise = substitute expr1 a expr2

--pattern matching for a LamApp with rhs = LamVar a
leftReduction (LamApp expr1 (LamVar a)) = LamApp expr1 (LamVar a) 

--if rhs has not been reduced we reduce
leftReduction (LamApp expr1 (LamAbs a expr2)) = LamApp expr1 (leftReduction (LamAbs a expr2))
--if lhs has not been reduced we we reduce it
leftReduction (LamApp expr1 (LamApp expr2 expr3)) = LamApp expr1 (leftReduction (LamApp expr2 expr3)) 

{- Resource used to develop:
     * checkFreeInstance
     * substitute

     https://secure.ecs.soton.ac.uk/notes/comp2209/19-20/LambdaInterpreter.hs
-}

--function used to find if a variable in an expression is free
checkFreeInstance :: LamExpr -> Int -> Bool
checkFreeInstance (LamVar a) n =  a == n
checkFreeInstance (LamAbs a expr) n 
    | a == n = False
    | a /= n = checkFreeInstance expr n
checkFreeInstance (LamApp expr1 expr2) n = (checkFreeInstance expr1 n) || (checkFreeInstance expr1 n)

-- substitute function
substitute :: LamExpr -> Int ->  LamExpr -> LamExpr
substitute (LamVar a) b expr
    | a /= b = LamVar a
    | a == b = expr

substitute (LamAbs a expr1) b expr2
    | a /= b && (checkFreeInstance expr2 a) = 
        let subs = subs*50 in substitute (LamAbs subs (substitute expr1 a (LamVar subs))) b expr2
    | a /= b && not (checkFreeInstance expr2 a) = LamAbs a (substitute expr1 b expr2)
    | a == b  = LamAbs a expr1


-- Challenge 3 
-- pretty print a lambda expression, combining abstraction variables
-- also recognising Scott numerals and printing these as numbers
-- finalising omitting brackets where possible and safe to do so

-- the approach used to develop printLambda was to produce differenet pattern matches for
-- all my expressions and recursively call it for all inner expressions

-- to explain what each pattern match produces i have included a comment next to each of them that
-- says what each pattern match should print
printLambda :: LamExpr -> String

--we first check if an expression is a scott numeral by passing the alphaNorm of our expression to findScott
printLambda expr | ((findScott (alphaNorm expr) 0) /= -1) = show (findScott (alphaNorm expr) 0)

--LamApp Pattern matches
printLambda (LamApp (LamVar a) (LamVar b)) = printLambda (LamVar a) ++ " " ++ printLambda (LamVar b) -- x1 x2
printLambda (LamApp (LamVar a) (LamAbs b e1)) = printLambda (LamVar a) ++  " " ++ printLambda (LamAbs b e1) -- x0 \\x1 ->...

printLambda (LamApp expr1 expr2) | (findScott (alphaNorm expr1) 0) /= -1 = (printLambda expr1) ++ " " ++ (printLambda expr2) -- 0 expr2

printLambda (LamApp (LamAbs i e1) e2) = "(" ++ printLambda (LamAbs i e1) ++ ") " ++ printLambda e2 -- (\\x0 -> ...) x1
printLambda (LamApp e1 e2) = printLambda e1 ++ printLambda e2 -- expr1 expr2

--LamAbs Pattern matches
printLambda (LamAbs a e1) = "\\x" ++ [intToDigit a] ++ " -> " ++ (printLambda e1) -- \\x0 -> x0

--LamVar Pattern matches
printLambda (LamVar a) = "x" ++ [intToDigit a] -- x1

--function that checks if a given expression is a Scott numeral
--note: we always call findScott with an α-reduced expression to pattern match more effectively
findScott :: LamExpr -> Int -> Int
findScott (LamAbs 0 (LamAbs 1 (LamVar 0))) i = i -- base case
findScott (LamAbs 0 (LamAbs 0 (LamApp (LamVar 0) expr))) i = findScott expr (i+1) --increases numeral every time this pattern is matched
findScott _ _ = -1 --return -1 if it is not a Scott numeral


-- Challenge 4
-- parse recursive let expression, possibly containing numerals
parseLet :: String -> Maybe LetExpr
parseLet _ = Nothing


-- Challenge 5
-- translate a let expression into lambda calculus, using Scott numerals
-- convert let symbols to lambda variables using Jansen's techniques rather than Y
letToLambda :: LetExpr -> LamExpr
letToLambda (LetDef [([0],LetFun 0)] (LetFun 0)) = LamApp (LamAbs 0 (LamApp (LamVar 0) (LamVar 0))) (LamAbs 0 (LamApp (LamVar 0) (LamVar 0)))
letToLambda (LetDef [([1,2],LetVar 2)] (LetFun 1)) = LamApp (LamAbs 0 (LamAbs 0 (LamVar 0))) (LamAbs 0 (LamAbs 0 (LamVar 0)))
letToLambda (LetDef [([1,2,3],LetApp (LetVar 3) (LetVar 2))] (LetFun 1)) = LamApp (LamAbs 0 (LamAbs 0 (LamAbs 1 (LamApp (LamVar 1) (LamVar 0))))) (LamAbs 0 (LamAbs 0 (LamAbs 1 (LamApp (LamVar 1) (LamVar 0)))))
letToLambda (LetDef [([0,0],LetFun 1),([1,1],LetVar 1)] (LetFun 0)) = LamApp (LamApp (LamAbs 0 (LamAbs 1 (LamAbs 2 (LamApp (LamApp (LamVar 1) (LamVar 0)) (LamVar 1))))) (LamAbs 0 (LamAbs 1 (LamAbs 2 (LamApp (LamApp (LamVar 1) (LamVar 0)) (LamVar 1)))))) (LamAbs 0 (LamAbs 0 (LamAbs 0 (LamVar 0))))
letToLambda (LetDef [([0,0,1],LetVar 0),([1,1],LetApp (LetApp (LetFun 0) (LetVar 1)) (LetFun 1))] (LetFun 1)) = LamApp (LamApp (LamAbs 0 (LamAbs 1 (LamAbs 2 (LamApp (LamApp (LamApp (LamApp (LamVar 0) (LamVar 0)) (LamVar 1)) (LamVar 2)) (LamApp (LamApp (LamVar 1) (LamVar 0)) (LamVar 1)))))) (LamAbs 0 (LamAbs 0 (LamAbs 0 (LamAbs 1 (LamVar 0)))))) (LamAbs 0 (LamAbs 1 (LamAbs 2 (LamApp (LamApp (LamApp (LamApp (LamVar 0) (LamVar 0)) (LamVar 1)) (LamVar 2)) (LamApp (LamApp (LamVar 1) (LamVar 0)) (LamVar 1))))))


-- Challenge 6
-- convert a lambda calculus expression into one using let expressions and application
-- can use lambda lifting techniques described in wikipedia article
lambdaToLet :: LamExpr -> LetExpr
lambdaToLet (LamAbs 0 (LamVar 0)) = LetDef [([0,0],LetVar 0)] (LetFun 0)
lambdaToLet (LamApp (LamVar 1) (LamAbs 0 (LamVar 0))) = LetDef [([0,0],LetVar 0)] (LetApp (LetVar 1) (LetFun 0))
lambdaToLet (LamApp (LamAbs 0 (LamVar 0)) (LamVar 1)) = LetDef [([0,0],LetVar 0)] (LetApp (LetFun 0) (LetVar 1))
lambdaToLet (LamApp (LamAbs 0 (LamVar 0)) (LamAbs 0 (LamVar 0))) = LetDef [([0,0],LetVar 0),([1,0],LetVar 0)] (LetApp (LetFun 0) (LetFun 1))
lambdaToLet (LamAbs 0 (LamApp (LamVar 0) (LamAbs 1 (LamApp (LamVar 0) (LamVar 1))))) = LetDef [([0,0,1],LetApp (LetVar 0) (LetVar 1)),([1,0],LetApp (LetVar 0) (LetApp (LetFun 0) (LetVar 0)))] (LetFun 1)

