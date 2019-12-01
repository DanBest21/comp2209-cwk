-- Example for lecture to demonstrate simple monadic parsing
import Parsing

data BExp = Tru | Fls | Var String | And BExp BExp | Or BExp BExp
   deriving (Eq,Show)

type Substitution = [ (String, Bool) ]

check :: Maybe a -> a
check Nothing = error ("No binding found for variable ")
check (Just b) = b

-- evaluation function to provide semantics to formulas
eval :: Substitution -> BExp -> Bool
eval _ Tru = True
eval _ Fls = False
eval s (Var p) = check $ lookup p s
eval s (And e1 e2) = (eval s e1) && (eval s e2)
eval s (Or e1 e2)  = (eval s e1) || (eval s e2)

-- Parsing Code

-- Expressions
-- Define a parser for each kind of expression
-- We use "ident" and "symbol" from Parsing.hs
varExp :: Parser BExp
varExp = do s <- ident
            return (Var s)

truExp :: Parser BExp
truExp = do symbol "T"
            return (Tru)
 
flsExp :: Parser BExp
flsExp = do symbol "F" 
            return (Fls)

andExp :: Parser BExp
andExp = do e1 <- lowerExpr
            symbol "&" 
            e2 <- expr
            return (And e1 e2)

orExp :: Parser BExp
orExp = do e1 <- evenLowerExpr
           symbol "|"
           e2 <- lowerExpr
           return (Or e1 e2)

-- Define the top level entry point
-- use choice <|> to write alternatives in the grammar
expr :: Parser BExp
expr = andExp <|> lowerExpr 
lowerExpr = orExp <|> evenLowerExpr
evenLowerExpr = varExp <|> truExp <|> flsExp

-- Finally, define the actual function to parse input strings
-- NB, this definition is just for demonstration. It is not a good
-- definition and needs improving
parseBExp :: String -> BExp
parseBExp = fst . head . (parse expr)
