-- comp2209 Functional Programming Challenges
-- (c) University of Southampton 2019
-- Skeleton code to be updated with your solutions
-- The dummy functions here simply return a randome value that is usually wrong 

-- DO NOT MODIFY THE FOLLOWING LINES OF CODE
module Challenges (alphaNorm, countAllReds, printLambda, parseLet,
    LamExpr(LamApp, LamAbs, LamVar), LetExpr(LetApp, LetDef, LetFun, LetVar, LetNum))
where

-- Import standard library and parsing definitions from Hutton 2016, Chapter 13
import Data.Char
import Parsing

import qualified Data.Map
import qualified Data.List
import Data.Typeable

-- abstract data type for simple lambda calculus expressions
data LamExpr = LamApp LamExpr LamExpr  |  LamAbs Int LamExpr  |  LamVar Int deriving (Show, Eq)

-- abstract data type for simple let expressions
data LetExpr = LetApp LetExpr LetExpr  |  LetDef [([Int], LetExpr)] LetExpr |  LetFun Int | LetVar Int | LetNum Int deriving (Show, Eq)
-- END OF CODE YOU MUST NOT MODIFY

data Term = Var Int | Abstraction Int Term | Application Term Term deriving (Show, Eq)


-- ADD YOUR OWN CODE HERE

-------------------------------------------------------------------------------------------------------------
-- Challenge 1 ----------------------------------------------------------------------------------------------
-- generate the alpha normal form for a simple lambda calculus expression
-- each bound variable is chosen to be the first one possible
alphaNorm :: LamExpr -> LamExpr
alphaNorm expr = alphaReduce (rename expr (getFreeInstances expr)) 0


alphaReduce :: LamExpr -> Int -> LamExpr
alphaReduce (LamAbs a e1) c
    | getFreeInstances (LamAbs a e1) < getFreeInstances e1 =  (LamAbs c (alphaReduce (changeBound e1 a c) (c+1)))
    | otherwise =  (LamAbs c (alphaReduce e1 (c)))

alphaReduce (LamVar a) c = LamVar a

alphaReduce (LamApp (LamVar a) e2) c = LamApp (LamVar a) (alphaReduce e2 0)
alphaReduce (LamApp e1 e2) c = LamApp (alphaReduce e1 c) (alphaReduce e2 c)

getFreeInstances :: LamExpr -> [Int]
getFreeInstances (LamVar x) =  [x]
getFreeInstances (LamAbs x e) = Data.List.delete x $ getFreeInstances e
getFreeInstances (LamApp l r) = Data.List.nub $ getFreeInstances l ++ getFreeInstances r

changeBound :: LamExpr -> Int -> Int -> LamExpr
changeBound (LamVar a) b c | a == b = LamVar c
                           | otherwise = LamVar a

changeBound (LamAbs a expr) b c = (LamAbs a (changeBound expr b c))
changeBound (LamApp (LamVar a) expr2) b c | a < 0 = LamApp (changeBound (LamVar a) b c) expr2
changeBound (LamApp expr1 expr2) a b = (LamApp (changeBound expr1 a b) (changeBound expr2 a b))

rename :: LamExpr -> [Int] -> LamExpr
rename (LamVar a) fs
    | a `elem` fs = (LamVar a)
    | otherwise = (LamVar ((a+1)*(-50)))

rename (LamAbs a exp) fs = (LamAbs ((a+1)*(-50)) (rename exp fs))
rename (LamApp exp1 exp2) fs = (LamApp (rename exp1 fs) (rename exp2 fs))

-------------------------------------------------------------------------------------------------------------
-- Challenge 2 ----------------------------------------------------------------------------------------------
-- count all reduction paths for a given lambda expression m, of length up to a given limit l
-- Looked through examples of the checkFreeInstance, rename and substitute function in https://secure.ecs.soton.ac.uk/notes/comp2209/18-19/LambdaInterpreter.hs

countAllReds :: LamExpr -> Int -> Int
countAllReds _ n | n<0 = error "Can't have negative steps"
countAllReds _ 0 = 0
countAllReds expr 1
    | (leftReduction expr /= expr && rightReduction expr /= expr) = 0 -- If it is not reducible return 0
    | otherwise = 1
countAllReds expr n
    | (leftReduction expr == expr && rightReduction expr == expr) = 1
    | otherwise = length (generateReduced [expr] (n-1))

generateReduced :: [LamExpr] -> Int -> [LamExpr]
generateReduced seq i
    | i == 0 = [ e | e <- seq, ((e == leftReduction e) || (e == rightReduction e))]
    | otherwise = generateReduced (concat [ getReduction e | e <- seq ]) (i-1)


getReduction :: LamExpr -> [LamExpr]
getReduction expr
    | (rightReduction expr /= expr && leftReduction expr /= expr && leftReduction expr /= rightReduction expr) = [leftReduction expr, rightReduction expr]
    | (leftReduction expr == expr && rightReduction expr /= expr) = [rightReduction expr]
    | (leftReduction expr /= expr && leftReduction expr == expr) = [leftReduction expr]
    | otherwise = [leftReduction expr]


checkFreeInstance :: LamExpr -> Int -> Bool
checkFreeInstance (LamVar a) b = a == b
checkFreeInstance (LamAbs a expr) b 
    | a /= b = checkFreeInstance expr a
    | a == b = False
checkFreeInstance (LamApp expr1 expr2) a = (checkFreeInstance expr1 a) || (checkFreeInstance expr2 a)

-- Substitute Function 
substitute :: LamExpr -> Int ->  LamExpr -> LamExpr
substitute (LamVar a) b expr
    | a /= b = LamVar a
    | a == b = expr
substitute (LamAbs a expr1) b expr2
    | a /= b && (checkFreeInstance expr2 a)  = let x' = x'*27 in substitute (LamAbs x' (substitute expr1 a (LamVar x'))) b expr2
    | a /= b && not (checkFreeInstance expr2 a) = LamAbs a (substitute expr1 b expr2)
    | a == b  = LamAbs a expr1

rightReduction :: LamExpr -> LamExpr
rightReduction (LamVar a) = LamVar a
rightReduction (LamAbs a expr) = (LamAbs a (rightReduction expr))

rightReduction (LamApp (LamApp expr1 expr2) (LamVar a)) = LamApp (rightReduction app) var
     where
        app = (LamApp expr1 expr2)
        var = (LamVar a)

rightReduction(LamApp (LamApp expr1 expr2) expr3)
    | (expr3==rhs) = (LamApp (rightReduction app) expr3)
    | otherwise = (LamApp app rhs)
         where 
           rhs = rightReduction expr3
           app = LamApp expr1 expr2

rightReduction (LamApp (LamAbs a expr) (LamVar b)) = substitute expr a (LamVar b)
rightReduction (LamApp (LamAbs a expr1) expr2)
    | (expr2 == rhs) = substitute expr1 a expr2
    | otherwise = (LamApp (LamAbs a expr1) rhs)
         where
          rhs = rightReduction expr2

rightReduction (LamApp (LamVar a) expr) = LamApp var (rightReduction expr)
     where
        var = (LamVar a)

leftReduction :: LamExpr -> LamExpr 
leftReduction (LamVar a) = LamVar a
leftReduction (LamAbs a expr) = (LamAbs a (leftReduction expr))
leftReduction (LamApp (LamApp expr1 expr2) expr3) 
    | app == lhs = LamApp app (leftReduction expr3)
    | otherwise = LamApp lhs expr3
        where 
          lhs = leftReduction app
          app = (LamApp expr1 expr2)


leftReduction (LamApp e0@(LamAbs a expr1) expr2) | (lhs == expr1) =  substitute expr1 a expr2 -- If we cannot continue reducing we substitute
                                       | otherwise = LamApp (LamAbs a lhs) expr2 -- Otherwise, we reduce the right branch of the current left branch
                                        where lhs = leftReduction expr1

leftReduction (LamApp expr1 (LamApp expr2 expr3)) = LamApp expr1 (leftReduction (LamApp expr2 expr3)) -- Reducing the right application if nothing has been reduced
leftReduction (LamApp expr1 (LamVar a)) = LamApp expr1 (LamVar a) --  Case where the second is lam var and the first has not been reduced 
leftReduction (LamApp expr1 (LamAbs a expr2)) = LamApp expr1 (leftReduction (LamAbs a expr2)) -- Case where second is another abs we reduce e1


-------------------------------------------------------------------------------------------------------------
-- Challenge 3 ----------------------------------------------------------------------------------------------
-- pretty print a lambda expression, combining abstraction variables
-- also recognising Scott numerals and printing these as numbers
-- finalising omitting brackets where possible and safe to do so
printLambda :: LamExpr -> String

printLambda expr | ((findScott (alphaNorm expr) 0) /= -1) = show (findScott (alphaNorm expr) 0)

printLambda (LamApp (LamVar a) (LamVar b)) = printLambda (LamVar a) ++ " " ++ printLambda (LamVar b)
printLambda (LamApp (LamVar a) (LamAbs b e1)) = printLambda (LamVar a) ++  " " ++ printLambda (LamAbs b e1)
printLambda (LamApp (LamAbs i e1) e2) = "(" ++ printLambda (LamAbs i e1) ++ ") " ++ printLambda e2
printLambda (LamApp e1 e2) = printLambda e1 ++ printLambda e2


printLambda (LamAbs a e1) = "\\x" ++ [intToDigit a] ++ " -> " ++ (printLambda e1)
printLambda (LamVar a) = "x" ++ [intToDigit a]

findScott :: LamExpr -> Int -> Int
findScott (LamAbs 0 (LamAbs 1 (LamVar 0))) i = i
findScott (LamAbs 0 (LamAbs 0 (LamApp (LamVar 0) expr))) i = findScott expr (i+1)
findScott _ _ = -1


-------------------------------------------------------------------------------------------------------------
-- Challenge 4 ----------------------------------------------------------------------------------------------
-- parse recursive let expression, possibly containing numerals
parseLet :: String -> Maybe LetExpr
parseLet xs
    | checkNum xs = Just (LetNum x)
    | checkVar xs = Just (LetVar y)
    | checkFunc xs = Just (LetFun z)
    | checkDef xs = defenitionExtraction(tail(tail(tail(xs))))
    | checkApp xs = applicationExtraction xs
    | otherwise = Nothing
        where
            x = read(xs) :: Int
            y = read(tail(xs)) :: Int
            z = read(tail(xs)) :: Int
 
 
checkApp :: String -> Bool
checkApp [] = False
checkApp xs
    | length(xs) < 3 = False
    | head(tail(tail(tail(xs)))) == '(' = True
    | length(xs) >= 3 && helperCheckApp(helper2(xs)) = True
    | otherwise = False
        where
            helperCheckApp :: [String] -> Bool
            helperCheckApp (x:xs) | length(x:xs) == 1 && isExpression(x) = True
                | isExpression(x) = helperCheckApp(xs)
                | otherwise = False
            helper2 :: String -> [String] --here
            helper2 string2 = split ' ' string2
 
 
applicationExtraction :: String -> Maybe LetExpr
applicationExtraction string | head(string) /= 'x' &&
                               head(string) /= 'f'                          = Nothing
                             | isExpressionBracketed(head(aux1(string))) ||
                               isExpressionBracketed(last(aux1(string)))    =
                                 aux4(aux2(aux1(removeX ')' (removeX '(' (removeX 'x' string)))))
                             | length(aux1(string)) == 3 &&
                               head(string) == 'x'                          =
                                 aux3(aux2(aux1((removeX 'x' string))))
                             | otherwise                                    = Nothing
                              where
                                aux1 :: String -> [String]
                                aux1 string = split ' ' string
                                aux2 :: [String] -> [Int]
                                aux2 = map read
                                aux3 :: [Int] -> Maybe LetExpr
                                aux3 xs = Just (LetApp (LetApp (LetVar (head(xs)))
                                                               (LetVar (head(tail(xs))) ))
                                                               (LetVar (head(tail(tail(xs))))))
                                aux4 :: [Int] -> Maybe LetExpr
                                aux4 xs = Just (LetApp (LetVar (head(xs)))
                                               (LetApp (LetVar (head(tail(xs))))
                                               (LetVar (head(tail(tail(xs)))))))
checkDef :: String -> Bool
checkDef []                                                = False
checkDef string | length(string) < 19                       = False
                              | length(string) >= 19 &&
                                head(string) == 'l'&&
                                head(tail(string)) == 'e' &&
                                head(tail(tail(string))) == 't' &&
                                head(tail(tail(tail(string)))) == ' '&&
                                aux(tail(tail(tail(tail(string)))))            = True
                              | otherwise                                      = False
                                  where
                                    aux :: String -> Bool
                                    aux []                                                = False
                                    aux string1 | isEquationList(head(aux1(string1))) &&
                                                  checkApp(last(aux1(string1)))       = True
                                                | otherwise                               = False
                                    aux1 :: String -> [String]
                                    aux1 string2 = [init(head(aux2(string2)))] ++
                                                   [tail(tail(last(aux2(string2))))]
                                    aux2 :: String -> [String]
                                    aux2 string3 = split 'i' string3
 
defenitionExtraction :: String -> Maybe LetExpr
defenitionExtraction string | length(auxToInt(auxRemoval(head(aux1(string))))) >  3 = auxFinalSemi (auxToInt(auxRemoval(head(aux1(string)))))
                            | length(auxToInt(auxRemoval(head(aux1(string))))) == 3 = auxFinal (auxToInt(auxRemoval(head(aux1(string)))))
                            | otherwise                                             = Nothing
                              where
                                aux1 :: String -> [String]
                                aux1 string2 = [init(head(aux2(string2)))] ++
                                               [tail(tail(last(aux2(string2))))]
                                aux2 :: String -> [String]
                                aux2 string3 = split 'i' string3
                                auxRemoval :: String -> [String]
                                auxRemoval string3 = split ' ' (removeX ';' (removeX 'f' (removeX 'x' (removeX '=' string3))))
                                auxToInt :: [String] -> [Int]
                                auxToInt [] = []
                                auxToInt (x:xs) | x == ""   = auxToInt xs
                                                | otherwise = (read x :: Int) : rest
                                                  where rest = auxToInt xs
                                auxFinalSemi :: [Int] -> Maybe LetExpr
                                auxFinalSemi (x:xs) = Just (LetDef [([x,(head(xs))],LetVar (head(tail(xs)))),([(head(tail(tail(xs)))),(head(tail(tail(tail(xs)))))],LetVar (last(xs)))] (LetApp (LetFun r) (LetVar p)))
                                auxFinal :: [Int] -> Maybe LetExpr
                                auxFinal (x:xs) = Just (LetDef [([x,head(xs)],LetVar (last(xs)))] (LetApp (LetFun r) (LetVar p)))
                                p = read [last(last(aux1(string)))] :: Int
                                r = read [head(tail(last(aux1(string))))] :: Int
 
split :: Char -> String -> [String]
split _ [] = [""]
split sym (c:cs) | c == sym  = "" : rest
                 | otherwise = (c : head rest) : tail rest
        where rest = split sym cs
removeX :: Char -> String -> String
removeX _ []      = []
removeX c (x:xs) | c == x = removeX c xs
                | otherwise = x : removeX c xs
isExpressionBracketed :: String -> Bool
isExpressionBracketed string | head(string) == '(' ||
                               last(string) == ')'     = True
                             | otherwise               = False
 
isEquation :: String -> Bool
isEquation []                                 = False
isEquation string | length(string) < 9        = False
                  | length(aux1(string))  < 3 = False
                  | length(aux1(string)) >= 3 = aux string
                  | otherwise                 = False
                    where
                      aux :: String -> Bool
                      aux string1 | checkFunc(head(aux1(string1)))            &&
                                    isVariableList(unwords(init(tail(aux1(string1)))))   &&
                                    isExpression(last(aux1(string1)))                = True
                                  | otherwise                                        = False
                      aux1 :: String -> [String]
                      aux1 string2 = fst(head(aux2(string2))) ++ [tail(tail(snd(head(aux2(string2)))))]
                      aux2 :: String -> [([String], String)]
                      aux2 string3 = parse (identifier `sepby1` space) string3
 
isEquationList :: String -> Bool
isEquationList []                               = False
isEquationList string | length(string) < 9      = False
                      | length(split ';' (string)) < 1 = False
                      | length(split ';' (string)) >= 1 = aux(split ';' (string))
                      | otherwise                      = False
                        where
                          aux :: [String] -> Bool
                          aux []                                          = False
                          aux (x:xs) | length(x:xs) == 1 && isEquation(x) = True
                                     | isEquation(x)     = aux xs
                                     | otherwise         = False
 
isExpression :: String -> Bool
isExpression [] = False
isExpression string | checkNum string ||checkVar string ||checkFunc string || checkDef string      = True
                    | otherwise = False
 
checkFunc :: String -> Bool
checkFunc []                          = False
checkFunc (a:as) | length(a:as) <= 1  = False
                      | a /= 'f'                 = False
                      | checkNum as    = True
                      | otherwise                = False
isVariableList :: String -> Bool
isVariableList []                                = False
isVariableList string | length(string) <= 1      = False
                      | length(aux(string)) < 1  = False
                      | length(aux(string)) >= 1 = aux2(aux(string))
                      | otherwise                = False
                        where
                          aux :: String -> [String]
                          aux []      = []
                          aux string1 = fst(head(aux1(string1))) : aux (snd(head(aux1(string1))))
                          aux1 :: String -> [(String, String)]
                          aux1 string2 = parse identifier string2
                          aux2 :: [String] -> Bool
                          aux2 []                                                   = False
                          aux2 (x:xs) | length(x:xs) == 1 && checkVar x = True
                                      | checkVar x                      = aux2 xs
                                      | otherwise                                   = False
checkVar :: String -> Bool
checkVar []                          = False
checkVar (a:as) | length(a:as) <= 1  = False
                      | a /= 'x'                 = False
                      | checkNum as    = True
                      | otherwise                = False
 
checkNum :: String -> Bool
checkNum []                                                  = False
checkNum (x:xs) | length(x:xs) == 1                          = isExpressionDigit x
                    | length(x:xs) == 2 && (aux x) && aux(last(x:xs))  = True
                    | aux x                                            = checkNum xs
                    | otherwise                                        = False
                      where
                        aux :: Char -> Bool
                        aux c = Data.Char.isDigit(c)
                        isExpressionDigit :: Char -> Bool
                        isExpressionDigit x | length(parse digit [x]) == 0  = False
                                      | aux x                               = True
                                      | otherwise                           = False
sepby1 :: Parser a -> Parser b -> Parser [a]
p `sepby1` sep = do a <-p
                    as <- many (do {sep; p})
                    return (a:as)
