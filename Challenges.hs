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

-- Function adapted from the "free" function shown during the lecture on Interpreters (Subsitution) - (c) Julian Rathke, University of Southampton 2019 
isFree :: LamExpr -> Int -> Bool
isFree (LamApp e1 e2) x = (isFree e1 x) || (isFree e2 x)
isFree (LamAbs n e) x | x == n = False
                      | x /= n = isFree e x
isFree (LamVar n) x = x == n

-- Find the next free variable value, also considering free variables.
nextFreeVariable :: LamExpr -> Int -> Int
nextFreeVariable e n | isFree e n = nextFreeVariable e (n+1)
                     | otherwise  = n

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
-- - In the case that x == n, then leave it as it is.
-- - If x /= n, but x is bound to a value and n is already bound to something else, perform an alpha conversion that handles both accordingly.
-- - If x /= n, but x is bound to a value, then perform an alpha conversion, changing any value bound to this LamAbs.
-- - Else, if n is a free value, then perform an alpha conversion, changing any instance of that value to the next free value.
-- - Otherwise, n is a free value, and we are free to simply change this value to it.
-- Also check the LamApp to see if that value is already bound, in which case we want to pass the next free value across both expressions instead.
convertToANF :: LamExpr -> Int -> LamExpr
convertToANF (LamApp e1 e2) n | bIsFree1 && bIsFree2 = LamApp (convertToANF e1 free) (convertToANF e2 free)
                              | bIsFree1             = LamApp (convertToANF e1 0) (convertToANF e2 free)
                              | bIsFree2             = LamApp (convertToANF e1 free) (convertToANF e2 0)
                              | otherwise            = LamApp (convertToANF e1 0) (convertToANF e2 0)
                        where bIsFree1 = isFree e1 0
                              bIsFree2 = isFree e2 0
                              free = (nextFreeVariable (LamApp e1 e2) 0)
convertToANF (LamAbs x e) n | x == n                   = LamAbs x (convertToANF e n)
                            | bBoundOld && bBoundNew   = LamAbs n (convertToANF (alphaConversion (alphaConversion e free n) n x) n)
                            | bBoundOld                = LamAbs n (convertToANF (alphaConversion e n x) n)
                            | not(bBoundNew)           = LamAbs free (convertToANF (alphaConversion e free x) free)
                            | otherwise                = LamAbs n (convertToANF e n)
                        where bBoundOld = isBound (LamAbs x e) x (False)
                              bBoundNew = isBound (LamAbs x e) n (False)
                              free = nextFreeVariable (LamAbs x e) n
convertToANF (LamVar x) n = LamVar x

alphaNorm :: LamExpr -> LamExpr
alphaNorm e = convertToANF e 0

-- Challenge 2
-- Count all reduction paths for a given lambda expression m, of length up to a given limit l

data Direction = L Bool (LamExpr) | R Bool (LamExpr) deriving (Show, Eq)
type Trail = [Direction]
type Zipper = (LamExpr, Trail) 

-- Functions adapted from code given during the lecture on Trees - (c) Julian Rathke, University of Southampton 2019
goLeft, goRight, goUp :: Zipper -> Zipper
goLeft (LamApp l r, ts) = (l, L (False) r : ts)
goRight (LamApp l r, ts) = (r, R (False) l : ts)
goRight (LamAbs l r, ts) = (r, R (True) (LamVar l) : ts)
goUp (t, L b r : ts) = (LamApp t r, ts)
goUp (t, R (False) l : ts) = (LamApp l t, ts)
goUp (t, R (True) (LamVar l) : ts) = (LamAbs l t, ts)

-- Function adapted from code given during the lecture on Trees - (c) Julian Rathke, University of Southampton 2019
goRoot :: Zipper -> Zipper
goRoot (t, []) = (t, [])
goRoot z = goRoot $ goUp z

-- Function adapted from the "subst" function shown during the lecture on Interpreters (Subsitution) - (c) Julian Rathke, University of Southampton 2019
betaConversion :: LamExpr -> Int -> LamExpr -> LamExpr
betaConversion (LamApp e1 e2) n e = LamApp (betaConversion e1 n e) (betaConversion e2 n e)
betaConversion (LamAbs x e1) n e | x /= n && not(bFree) = LamAbs x (betaConversion e1 n e)
                                 | x /= n && bFree      = betaConversion (LamAbs free (betaConversion e1 x (LamVar free))) n e
                                 | x == n               = LamAbs x e1
                     where bFree = isFree e x
                           free = nextFreeVariable e n
betaConversion (LamVar x) n e | x == n    = e
                              | otherwise = LamVar x

-- Performs a left beta reduction on the passed expression .
leftReduction :: LamExpr -> LamExpr
leftReduction (LamApp (LamAbs x e) e2) = betaConversion e x e2
leftReduction (LamApp e1 e2) = LamApp (leftReduction e1) (e2)
leftReduction (LamAbs x e) = LamAbs x (leftReduction e)
leftReduction (LamVar x) = LamVar x

-- Performs a right beta reduction on the passed expression.
rightReduction :: LamExpr -> LamExpr
rightReduction (LamApp (LamAbs x e) e2) = betaConversion e x e2
rightReduction (LamApp e1 e2) = LamApp (e1) (rightReduction e2)
rightReduction (LamAbs x e) = LamAbs x (rightReduction e)
rightReduction (LamVar x) = LamVar x

-- Since a free variable on its own is already in ANF, this helper function is used to test equality for single variables.
handleSingleVariable :: LamExpr -> LamExpr
handleSingleVariable (LamVar x) = LamVar 0
handleSingleVariable e = e

-- Converts a given expression to its BNF by applying left and right beta reductions until the same result is given.
convertToBNF :: LamExpr -> LamExpr
convertToBNF e | isBNF     = e
               | left /= e = convertToBNF left
               | otherwise = convertToBNF right
            where left = leftReduction e
                  right = rightReduction e
                  isBNF = (e == left) && (e == right)

-- Takes the LamExpr out of the Zipper.
extractExpression :: Zipper -> LamExpr
extractExpression (e, ts) = alphaNorm e

-- Gets all the possible reductions in a list of Zippers by performing left and right reductions at each stage.
-- If the expression is in BNF already, it will be returned as a singleton. 
possibleReductions :: Zipper -> LamExpr -> [Zipper]
possibleReductions z@(LamApp (LamVar x) r, ts) e = possibleReductions (goRight z) e 
possibleReductions z@(LamApp l r, ts) e | bLeft     = [goRoot(leftReduction (LamApp l r), ts)] ++ possibleReductions (goRight z) e
                                        | bRight    = [goRoot(rightReduction (LamApp l r), ts)] ++ possibleReductions (goLeft z) e
                                        | otherwise = possibleReductions (goLeft z) e ++ possibleReductions (goRight z) e
            where bLeft = (goRoot(leftReduction (LamApp l r), ts) /= goRoot z)
                  bRight = (goRoot(rightReduction (LamApp l r), ts) /= goRoot z)
possibleReductions z@(LamAbs x r, ts) e = possibleReductions (goRight z) e
possibleReductions z e | bBNF      = [root]
                       | otherwise = []
            where bnf = alphaNorm (convertToBNF e)
                  root = goRoot z
                  rootExp = extractExpression root
                  bBNF = (rootExp == bnf)

-- Filters out all duplicate reductions that aren't already in BNF (since these need to be counted).
filterDuplicates :: [Zipper] -> LamExpr -> [Zipper]
filterDuplicates zs e = [ z | z@(e', ts) <- zs, alphaNorm (e') == bnf ] ++ nub [ z | z@(e', ts) <- zs, alphaNorm (e') /= bnf ]
            where bnf = alphaNorm (convertToBNF e)

-- Gets all possible reductions given a list of Zippers.
possibleReductionsList :: [Zipper] -> LamExpr -> [Zipper]
possibleReductionsList (z:[]) e = filterDuplicates (possibleReductions z e) e
possibleReductionsList (z:zs) e = filterDuplicates (possibleReductions z e) e ++ possibleReductionsList zs e

-- Performs reductions to a given limit.
possibleReductionsToLimit :: [Zipper] -> Int -> LamExpr -> [Zipper]
possibleReductionsToLimit zs 0 e = []
possibleReductionsToLimit zs 1 e = zs
possibleReductionsToLimit zs n e = possibleReductionsToLimit (possibleReductionsList zs e) (n-1) e

-- Counts the length of the list to determine the number of reduction paths to BNF.
countAllReds :: LamExpr -> Int -> Int
countAllReds e n | n < 0     = error "The value of n cannot be negative!"
                 | otherwise = length [ handleSingleVariable (alphaNorm x) | (x, ts) <- possibleReductionsToLimit [(e, [])] n e, handleSingleVariable (alphaNorm x) == bnf ]
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

-- Parses a single digit.
digitExp :: Parser Char
digitExp = do d <- digit
              return d

-- Parses multiple digits (at least one).
digitsExp :: Parser [Char]
digitsExp = do ds <- some digitExp
               return ds

-- Parses a number using the digitsExp function.
numExp :: Parser LetExpr
numExp = do n <- digitsExp
            return (LetNum (read n))

-- Parses a variable, and returns a LetVar.
varExp :: Parser LetExpr
varExp = do space
            char 'x'
            n <- digitsExp
            space
            return (LetVar (read n))
 
-- Parses a variable, and returns an Int.
varExp' :: Parser Int
varExp' = do space
             char 'x'
             n <- digitsExp
             space
             return (read n)

-- Parses a variable list, and returns a list of LetVars.
varListExp :: Parser [LetExpr]
varListExp = do vs <- some varExp
                return vs

-- Parses a variable list, and returns a list of Ints.
varListExp' :: Parser [Int]
varListExp' = do vs <- some varExp'
                 return vs

-- Parses a function, and returns a LetFun.
funExp :: Parser LetExpr
funExp = do space
            char 'f'
            n <- digitsExp
            space
            return (LetFun (read n))

-- Parses a function, and returns an Int.
funExp' :: Parser Int
funExp' = do space
             char 'f'
             n <- digitsExp
             space
             return (read n)

-- Parses a function, and returns a singleton of [([Int], LetExpr)]
eqnExp :: Parser [([Int], LetExpr)]
eqnExp = do f <- funExp'
            vs <- varListExp'
            space
            char '='
            space
            e <- expr
            return [(([f] ++ vs), e)]

-- Parses a function, and returns a [([Int], LetExpr)]
eqnListExp :: Parser [([Int], LetExpr)]
eqnListExp = do e <- eqnExp
                char ';'
                space
                es <- eqnListExp
                return (e ++ es)
            <|> eqnExp

-- Parses a let expression, and returns a LetDef.
letExp :: Parser LetExpr
letExp = do string "let"
            space
            es <- eqnListExp
            space
            string "in"
            e <- expr
            return (LetDef es e)

-- Parses anything in brackets separately.
bracketExp :: Parser LetExpr
bracketExp = do symbol "("
                e <- expr
                symbol ")"
                return e

-- Parses an application, using foldl1 to ensure left-associativity.
appExp :: Parser LetExpr
appExp = do es <- exprList
            return (foldl1 (\e1 -> \e2 -> LetApp e1 e2) es)

-- Parses a list of LetExpr
exprList :: Parser [LetExpr]
exprList = do es <- some expr1
              return es

-- A hierarchy of parsers to ensure there is no left-recursion.
expr :: Parser LetExpr
expr = appExp <|> expr1
expr1 = bracketExp <|> expr2
expr2 = letExp <|> expr3
expr3 = funExp <|> varExp <|> numExp

-- Performs the parse of the given String, handling the Maybe type around it.
parseLetExp :: Parser LetExpr -> String -> Maybe LetExpr
parseLetExp p s =
      case parse p s of
            [(res,rs)] -> Just res
            [] -> Nothing

parseLet :: String -> Maybe LetExpr
parseLet s = parseLetExp expr s

-- Challenge 5
-- Translate a let expression into lambda calculus, using Scott numerals
-- convert let symbols to lambda variables using Jansen's techniques rather than Y

formExpression :: [Int] -> LetExpr -> LamExpr
formExpression (x:xs) e = LamAbs x (formExpression xs e)
formExpression [] e = e'
            where e' = convertLetToLambda e (retrieveExprIds e)

markSubst :: LamExpr -> LamExpr
markSubst (LamApp e1 e2) = LamApp (markSubst (e1)) (markSubst (e2))
markSubst (LamAbs x e) = LamAbs (x + 10000) (markSubst e)
markSubst (LamVar x) = LamVar (x + 10000)

unmarkSubst :: LamExpr -> LamExpr
unmarkSubst (LamApp e1 e2) = LamApp (unmarkSubst (e1)) (unmarkSubst (e2))
unmarkSubst (LamAbs x e) | x >= 10000 = LamAbs (x - 10000) (unmarkSubst e)
                         | otherwise = LamAbs x (unmarkSubst e)
unmarkSubst (LamVar x) | x >= 10000 = LamVar (x - 10000)
                       | otherwise = LamVar x

varSubst :: LamExpr -> Int -> LamExpr -> LamExpr
varSubst (LamVar x) y e | x == y = markSubst e
                        | x /= y = LamVar x
varSubst (LamAbs x e1) y e = LamAbs x (varSubst e1 y e)            
varSubst (LamApp e1 e2) y e = LamApp (varSubst e1 y e) (varSubst e2 y e)

formExpr :: [LamExpr] -> LamExpr
formExpr es = foldl1 (\e1 -> \e2 -> LamApp (e1) (e2)) es

formVars :: [Int] -> [LamExpr]
formVars [] = []
formVars (x:xs) = [LamVar x] ++ (formVars xs)

formExprList :: [Int] -> [Int] -> [(Int, LamExpr)]
formExprList [] ys = []
formExprList (x:xs) ys = [(x, formExpr $ formVars ([x] ++ ys))] ++ formExprList xs ys

formFuncExprList :: [(Int, LamExpr)] -> [(Int, LamExpr)] -> [(Int, LamExpr)]
formFuncExprList [] ys = []
formFuncExprList (x@(n, e):xs) ys = [(n, formExpr ([e] ++ fmap (snd) ys))] ++ formFuncExprList xs ys

parallelSubst' :: LamExpr -> [Int] -> Int -> LamExpr -> Bool -> LamExpr
parallelSubst' f [] n e b = f
parallelSubst' f xs n e (True) = f
parallelSubst' f (x:xs) n e b | n == x    = parallelSubst' (varSubst f x e) xs n e (True)
                              | otherwise = parallelSubst' f xs n e b

parallelSubst :: LamExpr -> [Int] -> [(Int, LamExpr)] -> LamExpr
parallelSubst f xs [] = f
parallelSubst f xs (e@(n,e'):es) = parallelSubst s xs es
            where s = parallelSubst' f xs n e' (False)

handleLetExpr' :: [([Int], LetExpr)] -> [Int] -> [(Int, LamExpr)]
handleLetExpr' [] ys = []
handleLetExpr' (x@(n:ns, e1):xs) ys = [(n + 1000, unmarkSubst $ parallelSubst f ys (formExprList ys ys))] ++ handleLetExpr' xs ys
            where f = formExpression (ys ++ ns) (e1)

handleLetExpr :: [([Int], LetExpr)] -> [[Int]] -> LetExpr -> LamExpr
handleLetExpr xs yss e = unmarkSubst $ parallelSubst (convertLetToLambda e yss) ys fs
            where ys = retrieveFunctionIds yss
                  f' = handleLetExpr' xs ys
                  fs = formFuncExprList f' f'

formScottEncoding :: Int -> LamExpr
formScottEncoding 0 = LamAbs 0 (LamAbs 1 (LamVar 0))
formScottEncoding n = LamAbs 0 (LamAbs 1 (LamApp (LamVar 1) (formScottEncoding (n-1))))

convertLetToLambda :: LetExpr -> [[Int]] -> LamExpr
convertLetToLambda (LetDef (es) (e)) yss = handleLetExpr es yss e
convertLetToLambda (LetApp e1 e2) yss = LamApp (convertLetToLambda e1 yss) (convertLetToLambda e2 yss)
convertLetToLambda (LetVar x) yss = LamVar x
convertLetToLambda (LetFun x) yss = LamVar (x + 1000)
convertLetToLambda (LetNum x) yss = formScottEncoding x

retrieveFunctionIds :: [[Int]] -> [Int]
retrieveFunctionIds ((x:xs):xss) = [x + 1000] ++ retrieveFunctionIds xss
retrieveFunctionIds [] = []

retrieveExprIds :: LetExpr -> [[Int]]
retrieveExprIds (LetApp e1 e2) = retrieveExprIds e1 ++ retrieveExprIds e2
retrieveExprIds (LetDef ((xs, e1):[]) (e2)) = [xs] ++ retrieveExprIds e2
retrieveExprIds (LetDef ((xs, e1):xss) (e2)) = [xs] ++ retrieveExprIds (LetDef (xss) (e2)) ++ retrieveExprIds e1
retrieveExprIds e = []

letToLambda :: LetExpr -> LamExpr
letToLambda e = alphaNorm $ convertLetToLambda e (retrieveExprIds e)

-- Challenge 6
-- Convert a lambda calculus expression into one using let expressions and application
-- can use lambda lifting techniques described in wikipedia article
lambdaToLet :: LamExpr -> LetExpr
lambdaToLet _ = LetVar (-1)