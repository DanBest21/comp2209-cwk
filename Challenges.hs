-- COMP2209 Functional Programming Challenges
-- (c) Daniel Best, University of Southampton 2019

module Challenges (alphaNorm, countAllReds, printLambda, parseLet, letToLambda,
    LamExpr(LamApp, LamAbs, LamVar), LetExpr(LetApp, LetDef, LetFun, LetVar, LetNum),
    lambdaToLet) where

-- Import standard library and parsing definitions from Hutton 2016, Chapter 13
import Data.Char
import Data.List
import Parsing

-- abstract data type for simple lambda calculus expressions
data LamExpr = LamApp LamExpr LamExpr  |  LamAbs Int LamExpr  |  LamVar Int deriving (Show, Eq)

-- abstract data type for simple let expressions
data LetExpr = LetApp LetExpr LetExpr  |  LetDef [([Int], LetExpr)] LetExpr |  LetFun Int | LetVar Int | LetNum Int deriving (Show, Eq)

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
convertToANF (LamAbs x e) n | x == n && not(bBoundOld) = LamAbs x (convertToANF e n)
                            | x == n                   = LamAbs x (convertToANF e (n + 1))
                            | bBoundOld && bBoundNew   = LamAbs n (convertToANF (alphaConversion (alphaConversion e free n) n x) (n + 1))
                            | bBoundOld && bSecond     = LamAbs n (convertToANF (alphaConversion e n x) n)
                            | bBoundOld                = LamAbs n (convertToANF (alphaConversion e n x) (n + 1))
                            | not(bBoundNew)           = LamAbs n (convertToANF (alphaConversion e free n) free)
                            | otherwise                = LamAbs n (convertToANF e n)
                        where bBoundOld = isBound (LamAbs x e) x (False)
                              bBoundNew = isBound (LamAbs x e) n (False)
                              bSecond = isBound e x (False)
                              free = nextFreeVariable (LamAbs x e) n
convertToANF (LamVar x) n = LamVar x

alphaNorm :: LamExpr -> LamExpr
alphaNorm e = convertToANF e 0

-- Challenge 2
-- Count all reduction paths for a given lambda expression m, of length up to a given limit l

data Direction = L Bool (LamExpr) | R Bool (LamExpr) deriving (Show, Eq)
type Trail = [Direction]
type Zipper = (LamExpr, Trail) 

goLeft, goRight, goUp :: Zipper -> Zipper
goLeft (LamApp l r, ts) = (l, L (False) r : ts)
goRight (LamApp l r, ts) = (r, R (False) l : ts)
goRight (LamAbs l r, ts) = (r, R (True) (LamVar l) : ts)
goUp (t, L b r : ts) = (LamApp t r, ts)
goUp (t, R (False) l : ts) = (LamApp l t, ts)
goUp (t, R (True) (LamVar l) : ts) = (LamAbs l t, ts)

goRoot :: Zipper -> Zipper
goRoot (t, []) = (t, [])
goRoot z = goRoot $ goUp z

betaConversion :: LamExpr -> Int -> LamExpr -> LamExpr
betaConversion (LamApp e1 e2) n e = LamApp (betaConversion e1 n e) (betaConversion e2 n e)
betaConversion (LamAbs x e1) n e | x /= n && not(bFree) = LamAbs x (betaConversion e1 n e)
                                 | x /= n && bFree      = betaConversion (LamAbs free (betaConversion e1 x (LamVar free))) n e
                                 | x == n               = LamAbs x e1
                     where bFree = isBound e x (True)
                           free = nextFreeVariable e n
betaConversion (LamVar x) n e | x == n    = e
                              | otherwise = LamVar x

leftReduction :: LamExpr -> LamExpr
leftReduction (LamApp (LamAbs x e) e2) = betaConversion e x e2
leftReduction (LamApp e1 e2) = LamApp (leftReduction e1) (e2)
leftReduction (LamAbs x e) = LamAbs x e
leftReduction (LamVar x) = LamVar x

rightReduction :: LamExpr -> LamExpr
rightReduction (LamApp (LamAbs x e) e2) = betaConversion e x e2
rightReduction (LamApp e1 e2) = LamApp (e1) (rightReduction e2)
rightReduction (LamAbs x e) = LamAbs x e
rightReduction (LamVar x) = LamVar x

handleSingleVariable :: LamExpr -> LamExpr
handleSingleVariable (LamVar x) = LamVar 0
handleSingleVariable e = e

convertToBNF :: LamExpr -> LamExpr
convertToBNF e | isBNF     = e
               | left /= e = convertToBNF left
               | otherwise = convertToBNF right
            where left = leftReduction e
                  right = rightReduction e
                  isBNF = (e == left) && (e == right)

possibleReductions :: Zipper -> LamExpr -> [Zipper]
possibleReductions z@(LamApp l r, ts) e | bLeft     = [goRoot(leftReduction (LamApp l r), ts)] ++ possibleReductions (goLeft z) e ++ possibleReductions (goRight z) e
                                        | bRight    = [goRoot(rightReduction (LamApp l r), ts)] ++ possibleReductions (goLeft z) e ++ possibleReductions (goRight z) e
                                        | otherwise = possibleReductions (goLeft z) ++ possibleReductions (goRight z) e
            where bLeft = (goRoot(leftReduction (LamApp l r), ts) /= goRoot z)
                  bRight = (goRoot(rightReduction (LamApp l r), ts) /= goRoot z)
possibleReductions z@(LamAbs x r, ts) e = possibleReductions (goRight z) e
possibleReductions z e | bBNF      = [goRoot z]
                       | otherwise = []
            where bBNF = alphaNorm (convertToBNF e) == 

filterDuplicates :: [Zipper] -> LamExpr -> [Zipper]
filterDuplicates zs e = [ z | z@(e', ts) <- zs, alphaNorm (e') == bnf ] ++ nub [ z | z@(e', ts) <- zs, alphaNorm (e') /= bnf ]
            where bnf = alphaNorm (convertToBNF e)

possibleReductionsList :: [Zipper] -> LamExpr -> [Zipper]
possibleReductionsList (z:[]) e = filterDuplicates (possibleReductions z e) e
possibleReductionsList (z:zs) e = filterDuplicates (possibleReductions z e) e ++ possibleReductionsList zs e

possibleReductionsToLimit :: [Zipper] -> Int -> LamExpr -> [Zipper]
possibleReductionsToLimit zs 0 e = []
possibleReductionsToLimit zs 1 e = zs
possibleReductionsToLimit zs n e = possibleReductionsToLimit (possibleReductionsList zs e) (n-1) e

-- reductionsToLimit :: LamExpr -> Int -> LamExpr -> [LamExpr]
-- reductionsToLimit e1 0 e2 = []
-- reductionsToLimit (LamApp e1 e2) n e | n == 1         = [e]
--                                      | bEqual         = nub (reductionsToLimit left (n - 1) left ++ [LamApp (head (reductionsToLimit e1 n e)) e2] ++ [LamApp e1 (head (reductionsToLimit e2 n e))])
--                                      | otherwise      = nub (reductionsToLimit left (n - 1) left ++ reductionsToLimit right (n - 1) right ++ [LamApp (head (reductionsToLimit e1 n e)) e2] ++ [LamApp e1 (head (reductionsToLimit e2 n e))])
--             where left = leftReduction (LamApp e1 e2)
--                   right = rightReduction (LamApp e1 e2)
--                   bEqual = alphaNorm left == alphaNorm right
-- reductionsToLimit (LamAbs x e1) n e | n == 1    = [e]
--                                     | otherwise = [LamAbs x (head (reductionsToLimit e1 n e))]
-- reductionsToLimit (LamVar x) n e | n == 1    = [e]
--                                  | otherwise = [LamVar x]

-- countAllReds' :: LamExpr -> Int -> [LamExpr]
-- countAllReds' e n = [ handleSingleVariable (alphaNorm x) | x <- reductionsToLimit e n e ]

countAllReds :: LamExpr -> Int -> Int
countAllReds e n = (-1) -- length [ handleSingleVariable (alphaNorm x) | x <- reductionsToLimit e n e, handleSingleVariable x == bnf ]
            where bnf = handleSingleVariable (alphaNorm (convertToBNF e))

-- Challenge 3 
-- Pretty print a lambda expression, combining abstraction variables
-- also recognising Scott numerals and printing these as numbers
-- finalising omitting brackets where possible and safe to do so

-- Check to see if the provided expression is the Scott Encoding of a natural number, and returns that value if it is.
-- Otherwise, return -1 to indicate that it is not.
checkScottEncoding :: LamExpr -> Int -> Int
checkScottEncoding (LamAbs x (LamAbs y (LamVar z))) n | x == z    = n
                                                      | otherwise = -1
checkScottEncoding (LamAbs x (LamAbs y (LamApp (LamVar z) e))) n | y == z = checkScottEncoding e (n + 1)
                                                                 | otherwise         = -1
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
                  bLastAbs = right == (abstractionCount (LamAbs x e2) 0)
printExpression (LamApp (LamAbs x e) (LamApp e1 e2)) i = "(" ++ (printExpression (LamAbs x e) i) ++ ")" ++  " " ++ "(" ++ (printExpression (LamApp e1 e2) right) ++ ")"
            where right = abstractionCount (LamApp e1 e2) 0
printExpression (LamApp e (LamApp e1 e2)) i = (printExpression e i) ++ " " ++ "(" ++ (printExpression (LamApp e1 e2) right) ++ ")"
            where right = abstractionCount (LamApp e1 e2) 0
printExpression (LamApp (LamAbs x e) e2) i = "(" ++ (printExpression (LamAbs x e) i) ++ ")" ++ " " ++ (printExpression e2 right)
            where right = (i - (abstractionCount (LamAbs x e) 0))
printExpression (LamApp e1 (LamAbs x e)) i | bLastAbs  = (printExpression e1 i) ++ " " ++ (printExpression (LamAbs x e) right)
                                           | otherwise = (printExpression e1 i) ++ " " ++ "(" ++ (printExpression (LamAbs x e) right) ++ ")"
            where right = (i - (abstractionCount e1 0))
                  bLastAbs = right == (abstractionCount (LamAbs x e) 0)
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