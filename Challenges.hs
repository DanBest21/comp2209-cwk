-- COMP2209 Functional Programming Challenges
-- (c) Daniel Best, University of Southampton 2019
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
-- Generate the alpha normal form for a simple lambda calculus expression
-- each bound variable is chosen to be the first one possible

-- Checks to see if the value is bound, first by finding a LamAbs exists for it, and 
-- then finding a LamVar that it binds too.
isBound :: LamExpr -> Int -> Bool -> Bool
isBound (LamApp e1 e2) x b = (isBound e1 x b) || (isBound e2 x b)
isBound (LamAbs n e) x b | x == n || b == True = isBound e x (True)
                         | otherwise           = isBound e x (False)
isBound (LamVar n) x b | x == n && b = True
                       | otherwise   = False

-- Find the next free variable value, also considering free variables.
nextFreeVariable :: LamExpr -> Int -> Int
nextFreeVariable e n | isBound e n (True) = nextFreeVariable e (n+1)
                     | otherwise          = n

-- Perform an alpha conversion on the given m value, changing it to the value of n when found in a LamVar.
-- Ensure that any LamAbs that has this new n value is changed to m (these will be unbound).
alphaConversion :: LamExpr -> Int -> Int -> LamExpr
alphaConversion (LamApp e1 e2) n m = LamApp (alphaConversion e1 n m) (alphaConversion e2 n m)
alphaConversion (LamAbs x e) n m | x == n    = LamAbs m (alphaConversion e n m) 
                                 | otherwise = LamAbs x (alphaConversion e n m)
alphaConversion (LamVar x) n m | x == m    = LamVar n
                               | otherwise = LamVar x 

-- Convert an expression to ANF, handling each case for LamAbs accordingly:
-- - In the case that x == n but x isn't bound to anything, then leave it as it is.
-- - Otherwise, in all other cases x == n, then we need to increase the value of n by 1 for later conversions.
-- - If x /= n, but x is bound to a value, then perform an alpha conversion, changing any value bound to this LamAbs.
-- - Else, if n isn't a free value, then perform an alpha conversion, changing any instance of that value to the next free value.
-- - Otherwise, n is a free value, and we are free to simply change this value to it.
convertToANF :: LamExpr -> Int -> LamExpr
convertToANF (LamApp e1 e2) n = LamApp (convertToANF e1 n) (convertToANF e2 n)
convertToANF (LamAbs x e) n | x == n && not(bBound) = LamAbs x (convertToANF e n)
                            | x == n                = LamAbs x (convertToANF e (n + 1))
                            | bBound                = LamAbs n (convertToANF (alphaConversion e n x) (n + 1))
                            | not(bFree)            = LamAbs n (convertToANF (alphaConversion e free n) free)
                            | otherwise             = LamAbs n (convertToANF e n)
                        where bBound = isBound (LamAbs x e) x (False)
                              bFree = isBound (LamAbs x e) n (False)
                              free = nextFreeVariable (LamAbs x e) n
convertToANF (LamVar x) n = LamVar x

alphaNorm :: LamExpr -> LamExpr
alphaNorm e = convertToANF e 0

-- Challenge 2
-- Count all reduction paths for a given lambda expression m, of length up to a given limit l
countAllReds :: LamExpr -> Int -> Int
countAllReds _ _ = -1


-- Challenge 3 
-- Pretty print a lambda expression, combining abstraction variables
-- also recognising Scott numerals and printing these as numbers
-- finalising omitting brackets where possible and safe to do so
printLambda :: LamExpr -> String
printLambda _ = ""


-- Challenge 4
-- Parse recursive let expression, possibly containing numerals
parseLet :: String -> Maybe LetExpr
parseLet _ = Just (LetVar (-1))


-- Challenge 5
-- Translate a let expression into lambda calculus, using Scott numerals
-- convert let symbols to lambda variables using Jansen's techniques rather than Y
letToLambda :: LetExpr -> LamExpr
letToLambda _ = LamVar (-1)


-- Challenge 6
-- Convert a lambda calculus expression into one using let expressions and application
-- can use lambda lifting techniques described in wikipedia article
lambdaToLet :: LamExpr -> LetExpr
lambdaToLet _ = LetVar (-1)