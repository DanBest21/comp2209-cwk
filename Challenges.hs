-- comp2209 Functional Programming Challenges
-- (c) University of Southampton 2019
-- Skeleton code to be updated with your solutions
-- The dummy functions here simply return a random value that is usually wrong 

-- DO NOT MODIFY THE FOLLOWING LINES OF CODE
module Challenges (alphaNorm, countAllReds, printLambda, parseLet, letToLambda,
    LamExpr(LamApp, LamAbs, LamVar), LetExpr(LetApp, LetDef, LetFun, LetVar, LetNum),
    lambdaToLet) where

-- Import standard library and parsing definitions from Hutton 2016, Chapter 13
import Data.Char
import Parsing

-- abstract data type for simple lambda calculus expressions
data LamExpr = LamApp LamExpr LamExpr  |  LamAbs Int LamExpr  |  LamVar Int deriving (Show, Eq)

-- abstract data type for simple let expressions
data LetExpr = LetApp LetExpr LetExpr  |  LetDef [([Int], LetExpr)] LetExpr |  LetFun Int | LetVar Int | LetNum Int deriving (Show, Eq)
-- END OF CODE YOU MUST NOT MODIFY


-- ADD YOUR OWN CODE HERE
-- Challenge 1
-- generate the alpha normal form for a simple lambda calculus expression
-- each bound variable is chosen to be the first one possible
isBound :: LamExpr -> Int -> Bool -> Bool
isBound (LamApp e1 e2) x b = (isBound e1 x b) || (isBound e2 x b)
isBound (LamAbs n e) x b | x == n || b == True = isBound e x (True)
                         | otherwise           = isBound e x (False)
isBound (LamVar n) x b | x == n && b = True
                       | otherwise   = False

nextFreeVariable :: LamExpr -> Int -> Int
nextFreeVariable e n | isBound e n (True) = nextFreeVariable e (n+1)
                     | otherwise          = n

renameVariable :: LamExpr -> Int -> Int -> LamExpr
renameVariable (LamApp e1 e2) n m = LamApp (renameVariable e1 n m) (renameVariable e2 n m)
renameVariable (LamAbs x e) n m | x == n    = LamAbs m (renameVariable e n m) 
                                | otherwise = LamAbs x (renameVariable e n m)
renameVariable (LamVar x) n m | x == m    = LamVar n
                              | otherwise = LamVar x 

alphaConversion :: LamExpr -> Int -> LamExpr
alphaConversion (LamApp e1 e2) n = LamApp (alphaConversion e1 n) (alphaConversion e2 n)
alphaConversion (LamAbs x e) n | x == n && not(bBound) = LamAbs x (alphaConversion e n)
                               | x == n                = LamAbs x (alphaConversion e (n + 1))
                               | bBound                = LamAbs n (alphaConversion (renameVariable e n x) (n + 1))
                               | bFree                 = LamAbs n (alphaConversion (renameVariable e free n) free)
                               | otherwise             = LamAbs n (alphaConversion e n)
                        where bBound = isBound (LamAbs x e) x (False)
                              bFree = not(isBound (LamAbs x e) n (False))
                              free = nextFreeVariable (LamAbs x e) n
alphaConversion (LamVar x) n = LamVar x

alphaNorm :: LamExpr -> LamExpr
alphaNorm e = alphaConversion e 0

-- Challenge 2
-- count all reduction paths for a given lambda expression m, of length up to a given limit l
countAllReds :: LamExpr -> Int -> Int
countAllReds _ _ = -1


-- Challenge 3 
-- pretty print a lambda expression, combining abstraction variables
-- also recognising Scott numerals and printing these as numbers
-- finalising omitting brackets where possible and safe to do so
printLambda :: LamExpr -> String
printLambda _ = ""


-- Challenge 4
-- parse recursive let expression, possibly containing numerals
parseLet :: String -> Maybe LetExpr
parseLet _ = Just (LetVar (-1))


-- Challenge 5
-- translate a let expression into lambda calculus, using Scott numerals
-- convert let symbols to lambda variables using Jansen's techniques rather than Y
letToLambda :: LetExpr -> LamExpr
letToLambda _ = LamVar (-1)


-- Challenge 6
-- convert a lambda calculus expression into one using let expressions and application
-- can use lambda lifting techniques described in wikipedia article
lambdaToLet :: LamExpr -> LetExpr
lambdaToLet _ = LetVar (-1)