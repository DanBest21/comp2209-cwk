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
-- Ensure that any LamAbs that has this new n value is changed to m (these will be unbound), and vice versa.
alphaConversion :: LamExpr -> Int -> Int -> LamExpr
alphaConversion (LamApp e1 e2) n m = LamApp (alphaConversion e1 n m) (alphaConversion e2 n m)
alphaConversion (LamAbs x e) n m | x == m    = LamAbs n (alphaConversion e n m) 
                                 | x == n    = LamAbs m (alphaConversion e n m) 
                                 | otherwise = LamAbs x (alphaConversion e n m)
alphaConversion (LamVar x) n m | x == m    = LamVar n
                               | otherwise = LamVar x 

-- Convert an expression to ANF, handling each case for LamAbs accordingly:
-- - In the case that x == n but x isn't bound to anything, then leave it as it is.
-- - Otherwise, in all other cases x == n, then we need to increase the value of n by 1 for later conversions.
-- - If x /= n, but x is bound to a value and n is already bound to something else, perform an alpha conversion that handles both accordingly.
-- - If x /= n, but x is bound to a value, then perform an alpha conversion, changing any value bound to this LamAbs.
-- - Else, if n has a free value, then perform an alpha conversion, changing any instance of that value to the next free value.
-- - Otherwise, n is a free value, and we are free to simply change this value to it.
-- Also check the LamApp to see if that value is already bound, in which case we want to pass the next free value across both expressions instead.
convertToANF :: LamExpr -> Int -> LamExpr
convertToANF (LamApp e1 e2) n | bIsBound1 && bIsBound2 = LamApp (convertToANF e1 free) (convertToANF e2 free)
                              | bIsBound1              = LamApp (convertToANF e1 n) (convertToANF e2 free)
                              | bIsBound2              = LamApp (convertToANF e1 free) (convertToANF e2 n)
                              | otherwise              = LamApp (convertToANF e1 n) (convertToANF e2 n)
                        where bIsBound1 = isBound e1 n (False)
                              bIsBound2 = isBound e2 n (False)
                              free = (nextFreeVariable (LamApp e1 e2) n)
convertToANF (LamAbs x e) n | x == n && not(bBound) = LamAbs x (convertToANF e n)
                            | x == n                = LamAbs x (convertToANF e (n + 1))
                            | bBound && bFree       = LamAbs n (convertToANF (alphaConversion (alphaConversion e free n) n x) (n + 1))
                            | bBound && bSecond     = LamAbs n (convertToANF (alphaConversion e n x) n)
                            | bBound                = LamAbs n (convertToANF (alphaConversion e n x) (n + 1))
                            | not(bFree)            = LamAbs n (convertToANF (alphaConversion e free n) free)
                            | otherwise             = LamAbs n (convertToANF e n)
                        where bBound = isBound (LamAbs x e) x (False)
                              bFree = isBound (LamAbs x e) n (False)
                              bSecond = isBound e x (False)
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

-- Check to see if the provided expression is the Scott Encoding of a natural number, and returns that value if it is.
-- Otherwise, return -1 to indicate that it is not.
checkScottEncoding :: LamExpr -> Int -> Int
checkScottEncoding (LamAbs x (LamAbs y (LamVar z))) n = n
checkScottEncoding (LamAbs x (LamAbs y (LamApp (LamVar z) e))) n = checkScottEncoding e (n + 1)
checkScottEncoding _ n = -1

-- Get the number of abstractions (LamAbs) in the given expression.
abstractionCount :: LamExpr -> Int -> Int
abstractionCount (LamApp e1 e2) i = (abstractionCount e1 i) + (abstractionCount e2 0)
abstractionCount (LamAbs x e) i = abstractionCount e (i + 1)
abstractionCount (LamVar x) i = i

-- Do some pattern matching to check where to put brackets - abstractions associate to the right, and application associates to the left (more tightly).
-- Use the i variable to determine how many abstraction values are left - the rightmost abstraction in the expression should not be in brackets.
printExpression :: LamExpr -> Int -> String
printExpression (LamApp (LamAbs x e1) (LamAbs y e2)) i | bLastAbs  = "(" ++ (printExpression (LamAbs x e1) i) ++ ")" ++ " " ++ (printExpression (LamAbs y e2) right)
                                                       | otherwise = "(" ++ (printExpression (LamAbs x e1) i) ++ ")" ++ " " ++ "(" ++ (printExpression (LamAbs y e2) right) ++ ")"
            where right = (i - (abstractionCount (LamAbs x e1) 0))
                  bLastAbs = right == 1
printExpression (LamApp (LamAbs x e) (LamApp e1 e2)) i = "(" ++ (printExpression (LamAbs x e) i) ++ ")" ++  " " ++ "(" ++ (printExpression (LamApp e1 e2) right) ++ ")"
            where right = (i - (abstractionCount (LamAbs x e) 0))
printExpression (LamApp e (LamApp e1 e2)) i = (printExpression e i) ++ " " ++ "(" ++ (printExpression (LamApp e1 e2) right) ++ ")"
            where right = (i - (abstractionCount e 0))
printExpression (LamApp (LamAbs x e) e2) i = "(" ++ (printExpression (LamAbs x e) i) ++ ")" ++ " " ++ (printExpression e2 right)
            where right = (i - (abstractionCount (LamAbs x e) 0))
printExpression (LamApp e1 (LamAbs x e)) i | bLastAbs  = (printExpression e1 i) ++ " " ++ (printExpression (LamAbs x e) right)
                                           | otherwise = (printExpression e1 i) ++ " " ++ "(" ++ (printExpression (LamAbs x e) right) ++ ")"
            where right = (i - (abstractionCount e1 0))
                  bLastAbs = right == 1
printExpression (LamApp e1 e2) i = (printExpression e1 i) ++ " " ++ (printExpression e2 right)
            where right = (i - (abstractionCount e1 0))
printExpression (LamAbs x e) i = "\\x" ++ (show x) ++ " -> " ++ (printExpression e (i - 1))
printExpression (LamVar x) i = "x" ++ (show x)

printLambda :: LamExpr -> String
printLambda e | scottEncoding == -1 = printExpression e (abstractionCount e 0)
              | otherwise           = show scottEncoding
            where scottEncoding = checkScottEncoding e 0

-- Challenge 4
-- Parse recursive let expression, possibly containing numerals

-- TEMP *************************************************************
-- varExp :: Parser BExp
-- varExp = do s <- ident
--             return (Var s)

-- truExp :: Parser BExp
-- truExp = do symbol "T"
--             return (Tru)
 
-- flsExp :: Parser BExp
-- flsExp = do symbol "F" 
--             return (Fls)

-- andExp :: Parser BExp
-- andExp = do e1 <- lowerExpr
--             symbol "&" 
--             e2 <- expr
--             return (And e1 e2)

-- orExp :: Parser BExp
-- orExp = do e1 <- evenLowerExpr
--            symbol "|"
--            e2 <- lowerExpr
--            return (Or e1 e2)
-- ****************************************************************

-- digitExp :: Parser Char
-- digitExp = do d <- digit
--               return d

-- digitsExp :: Parser [Char]
-- digitsExp = some digitExp

numExp :: Parser LetExpr
numExp = do n <- nat
            return (LetNum n)

varExp :: Parser LetExpr
varExp = do char 'x'
            n <- nat
            return (LetVar n)

funExp :: Parser LetExpr
funExp = do char 'f'
            n <- nat
            return (LetFun n)

-- varListExp :: Parser LetExpr
-- varListExp = 

-- expr :: Parser LetExpr
-- expr = 

parseLet :: String -> Maybe LetExpr
-- parseLet = fst . head . (parse expr)
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