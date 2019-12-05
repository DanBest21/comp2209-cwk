-- comp2209 Functional Programming Challenges
-- (c) University of Southampton 2019
-- Sample tests by Andy Gravell, Julian Rathke
-- DO NOT RE-DISTRIBUTE OR RE-POST

-- Import standard library and parsing definitions from Hutton 2016, Chapter 13
-- and solutions to challenges
import Data.Char
import Parsing
import Challenges


-- Main program
--
-- There is one simple test suite per exercise, each a list of assertions
-- These are only the published tests -- further, unseen tests will also be applied
--
simpleTests :: [[Bool]]
simpleTests =
    [ -- Challenge 1
      [ alphaNorm (LamApp (LamVar 1) (LamVar 0)) == LamApp (LamVar 1) (LamVar 0),
        alphaNorm (LamAbs 3 (LamVar 2)) == LamAbs 0 (LamVar 2),
        alphaNorm (LamAbs 0 (LamAbs 1 (LamVar 0))) == LamAbs 0 (LamAbs 1 (LamVar 0)),
        alphaNorm (LamAbs 1 (LamAbs 0 (LamVar 1))) == LamAbs 0 (LamAbs 1 (LamVar 0)),
        alphaNorm (LamAbs 1 (LamAbs 0 (LamVar 0))) == LamAbs 0 (LamAbs 0 (LamVar 0)),
        alphaNorm (LamAbs 0 (LamAbs 1 (LamAbs 2 (LamVar 0)))) == 
            LamAbs 0 (LamAbs 1 (LamAbs 1 (LamVar 0))),
        -- Additional tests
        alphaNorm (LamAbs 1 (LamVar 0)) == LamAbs 1 (LamVar 0),
        alphaNorm (LamAbs 2 (LamAbs 3 (LamApp (LamVar 1) (LamVar 2)))) == 
            LamAbs 0 (LamAbs 2 (LamApp (LamVar 1) (LamVar 0))),
        alphaNorm (LamAbs 0 (LamAbs 5 (LamAbs 1 (LamAbs 2 (LamApp (LamApp (LamAbs 0 (LamVar 4))(LamVar 3))(LamApp (LamAbs 0 (LamVar 0))(LamVar 0))))))) ==
            LamAbs 0 (LamAbs 1 (LamAbs 1 (LamAbs 1 (LamApp (LamApp (LamAbs 0 (LamVar 4)) (LamVar 3)) (LamApp (LamAbs 0 (LamVar 0)) (LamVar 0)))))),
        alphaNorm (LamAbs 0 (LamAbs 5 (LamAbs 1 (LamAbs 2 (LamApp (LamApp (LamAbs 2 (LamVar 2))(LamVar 0))(LamApp (LamAbs 3 (LamVar 4))(LamVar 3))))))) ==
            LamAbs 0 (LamAbs 1 (LamAbs 1 (LamAbs 1 (LamApp (LamApp (LamAbs 0 (LamVar 0)) (LamVar 0)) (LamApp (LamAbs 0 (LamVar 4)) (LamVar 3)))))),
        alphaNorm (LamAbs 2 (LamApp (LamVar 1) (LamAbs 0 (LamApp (LamVar 0) (LamAbs 0 (LamVar 0)))))) ==    
            LamAbs 0 (LamApp (LamVar 1) (LamAbs 0 (LamApp (LamVar 0) (LamAbs 0 (LamVar 0))))),   
        alphaNorm (LamAbs 0 (LamAbs 0 (LamVar 0))) == (LamAbs 0 (LamAbs 0 (LamVar 0)))
      ],
      [ -- Challenge 2
        countAllReds (LamAbs 0 (LamAbs 1 (LamVar 1))) 0 == 0,
        countAllReds (LamAbs 0 (LamAbs 1 (LamVar 1))) 1 == 1,
        countAllReds (LamAbs 0 (LamAbs 1 (LamVar 1))) 2 == 1,
        countAllReds (LamApp (LamAbs 0 (LamVar 0)) (LamAbs 1 (LamVar 1))) 0 == 0,
        countAllReds (LamApp (LamAbs 0 (LamVar 0)) (LamAbs 1 (LamVar 1))) 1 == 0,
        countAllReds (LamApp (LamAbs 0 (LamVar 0)) (LamAbs 1 (LamVar 1))) 2 == 1,
        countAllReds (LamApp (LamApp (LamAbs 0 (LamAbs 1 (LamVar 0))) (LamVar 3))(LamApp (LamAbs 4 (LamVar 4)) (LamVar 5))) 2 == 0,
        countAllReds (LamApp (LamApp (LamAbs 0 (LamAbs 1 (LamVar 0))) (LamVar 3))(LamApp (LamAbs 4 (LamVar 4)) (LamVar 5))) 3 == 1,
        countAllReds (LamApp (LamApp (LamAbs 0 (LamAbs 1 (LamVar 0))) (LamVar 3))(LamApp (LamAbs 4 (LamVar 4)) (LamVar 5))) 4 == 3,
        -- Additional tests
        countAllReds (LamAbs 0 (LamAbs 5 (LamAbs 1 (LamAbs 2 (LamApp (LamApp (LamAbs 2 (LamVar 2))(LamVar 0))(LamApp (LamAbs 3 (LamVar 4))(LamVar 3))))))) 2 == 0,
        countAllReds (LamAbs 0 (LamAbs 5 (LamAbs 1 (LamAbs 2 (LamApp (LamApp (LamAbs 2 (LamVar 2))(LamVar 0))(LamApp (LamAbs 3 (LamVar 4))(LamVar 3))))))) 3 == 2,
        countAllReds (LamAbs 0 (LamAbs 5 (LamAbs 1 (LamAbs 2 (LamApp (LamApp (LamAbs 2 (LamVar 2))(LamVar 0))(LamApp (LamAbs 3 (LamVar 4))(LamVar 3))))))) 4 == 2,
        countAllReds (LamApp (LamVar 0) (LamAbs 1 (LamVar 0))) 1 == 1,
        countAllReds (LamApp (LamVar 0) (LamAbs 1 (LamVar 0))) 2 == 1,
        countAllReds (LamApp (LamVar 0) (LamAbs 1 (LamVar 0))) 10 == 1
      ],
      [ -- Challenge 3 (but note that additional spaces will be accepted)
        printLambda (LamApp (LamVar 2) (LamVar 1)) == "x2 x1",
        printLambda (LamApp (LamAbs 1 (LamVar 1)) (LamAbs 1 (LamVar 1))) == 
            "(\\x1 -> x1) \\x1 -> x1",
        printLambda (LamAbs 1 (LamApp (LamVar 1) (LamAbs 1 (LamVar 1)))) == 
            "\\x1 -> x1 \\x1 -> x1", 
        printLambda (LamAbs 1 (LamAbs 2 (LamVar 1))) == "0",
        printLambda (LamAbs 1 (LamAbs 1 (LamApp (LamVar 1) (LamAbs 1 (LamAbs 2 (LamVar 1)))))) == "1",
        -- Additional tests
        printLambda (LamAbs 1 (LamAbs 1 (LamApp (LamVar 1) (LamAbs 1 (LamAbs 2 (LamApp (LamVar 2) (LamAbs 2 (LamAbs 3 (LamVar 2))))))))) == "2",
        printLambda (LamAbs 1 (LamAbs 1 (LamApp (LamVar 1) (LamAbs 1 (LamAbs 2 (LamApp (LamVar 2) (LamAbs 2 (LamAbs 3 (LamVar 4))))))))) ==
          "\\x1 -> \\x1 -> x1 \\x1 -> \\x2 -> x2 \\x2 -> \\x3 -> x4",
        printLambda (LamApp (LamApp (LamVar 0) (LamVar 1)) (LamVar 2)) == "x0 x1 x2",
        printLambda (LamApp (LamVar 0) (LamApp (LamVar 1) (LamVar 2))) == "x0 (x1 x2)",
        printLambda (LamApp (LamApp (LamAbs 0 (LamVar 0))  (LamAbs 1 (LamVar 1))) (LamAbs 2 (LamVar 2))) == "(\\x0 -> x0) (\\x1 -> x1) \\x2 -> x2",
        printLambda (LamApp (LamAbs 0 (LamVar 0)) (LamApp (LamAbs 1 (LamVar 1)) (LamAbs 2 (LamVar 2)))) == "(\\x0 -> x0) ((\\x1 -> x1) \\x2 -> x2)",
        printLambda (LamApp (LamApp (LamVar 0) (LamApp (LamAbs 1 (LamVar 1)) (LamAbs 2 (LamVar 2)))) (LamAbs 3 (LamVar 3))) == "x0 ((\\x1 -> x1) \\x2 -> x2) \\x3 -> x3",
        printLambda (LamAbs 0 (LamAbs 1 (LamApp (LamApp (LamVar 0) (LamVar 1)) (LamVar 0)))) == "\\x0 -> \\x1 -> x0 x1 x0",
        printLambda (LamAbs 0 (LamAbs 1 (LamApp (LamVar 0) (LamApp (LamVar 1) (LamVar 0))))) == "\\x0 -> \\x1 -> x0 (x1 x0)",
        printLambda (LamAbs 1 (LamAbs 2 (LamAbs 3 (LamAbs 4 (LamApp (LamVar 1) (LamApp (LamApp (LamVar 1) (LamVar 2)) (LamAbs 1 (LamVar 2)))))))) == 
            "\\x1 -> \\x2 -> \\x3 -> \\x4 -> x1 (x1 x2 \\x1 -> x2)",
        printLambda (LamAbs 1 (LamAbs 2 (LamApp (LamVar 1) (LamApp (LamApp (LamVar 11) (LamApp (LamAbs 3 (LamVar 5)) (LamAbs 2 (LamVar 2)) )) (LamAbs 1 (LamApp (LamAbs 3 (LamVar 3)) (LamAbs 4 (LamVar 4)))))))) ==
            "\\x1 -> \\x2 -> x1 (x11 ((\\x3 -> x5) \\x2 -> x2) \\x1 -> (\\x3 -> x3) \\x4 -> x4)"
      ],
      [ -- Challenge 4
        parseLet "let x1 = x2" == Nothing,
        parseLet "x1 (x2 x3)" == Just (LetApp (LetVar 1) (LetApp (LetVar 2) (LetVar 3))),
        parseLet "x1 x2 x3" == Just (LetApp (LetApp (LetVar 1) (LetVar 2)) (LetVar 3)),
        parseLet "let f1 x1 = x2 in f1 x1" == 
            Just (LetDef [([1,1],LetVar 2)] (LetApp (LetFun 1) (LetVar 1))),
        parseLet "let f1 x2 = x2; f2 x1 = x1 in f1 x1" ==
            Just (LetDef [([1,2],LetVar 2),([2,1],LetVar 1)] (LetApp (LetFun 1) (LetVar 1)))
      ],
      [ -- Challenge 5 (but note that equivalent answers will be accepted)
        letToLambda (LetDef [([0],LetFun 0)] (LetFun 0)) ==
          LamApp (LamAbs 0 (LamApp (LamVar 0) (LamVar 0))) (LamAbs 0 (LamApp (LamVar 0) (LamVar 0))),
        letToLambda (LetDef [([1,2],LetVar 2)] (LetFun 1)) ==
          LamApp (LamAbs 0 (LamAbs 0 (LamVar 0))) (LamAbs 0 (LamAbs 0 (LamVar 0))),
        letToLambda (LetDef [([1,2,3],LetApp (LetVar 3) (LetVar 2))] (LetFun 1)) ==
          LamApp (LamAbs 0 (LamAbs 0 (LamAbs 1 (LamApp (LamVar 1) (LamVar 0))))) (LamAbs 0 (LamAbs 0 (LamAbs 1 (LamApp (LamVar 1) (LamVar 0))))),
        letToLambda (LetDef [([0,0],LetFun 1),([1,1],LetVar 1)] (LetFun 0)) ==
          LamApp (LamApp (LamAbs 0 (LamAbs 1 (LamAbs 2 (LamApp (LamApp (LamVar 1) (LamVar 0)) (LamVar 1))))) (LamAbs 0 (LamAbs 1 (LamAbs 2 (LamApp (LamApp (LamVar 1) (LamVar 0)) (LamVar 1)))))) (LamAbs 0 (LamAbs 0 (LamAbs 0 (LamVar 0)))),
        letToLambda (LetDef [([0,0,1],LetVar 0),([1,1],LetApp (LetApp (LetFun 0) (LetVar 1)) (LetFun 1))] (LetFun 1)) ==
          LamApp (LamApp (LamAbs 0 (LamAbs 1 (LamAbs 2 (LamApp (LamApp (LamApp (LamApp (LamVar 0) (LamVar 0)) (LamVar 1)) (LamVar 2)) (LamApp (LamApp (LamVar 1) (LamVar 0)) (LamVar 1)))))) (LamAbs 0 (LamAbs 0 (LamAbs 0 (LamAbs 1 (LamVar 0)))))) (LamAbs 0 (LamAbs 1 (LamAbs 2 (LamApp (LamApp (LamApp (LamApp (LamVar 0) (LamVar 0)) (LamVar 1)) (LamVar 2)) (LamApp (LamApp (LamVar 1) (LamVar 0)) (LamVar 1))))))  
      ],
      [ -- Challenge 6 (but note that equivalent answers will be accepted)
        lambdaToLet (LamAbs 0 (LamVar 0)) ==
          LetDef [([0,0],LetVar 0)] (LetFun 0),
        lambdaToLet (LamApp (LamVar 1) (LamAbs 0 (LamVar 0))) ==
          LetDef [([0,0],LetVar 0)] (LetApp (LetVar 1) (LetFun 0)),
        lambdaToLet (LamApp (LamAbs 0 (LamVar 0)) (LamVar 1)) ==
          LetDef [([0,0],LetVar 0)] (LetApp (LetFun 0) (LetVar 1)),
        lambdaToLet (LamApp (LamAbs 0 (LamVar 0)) (LamAbs 0 (LamVar 0))) ==
          LetDef [([0,0],LetVar 0),([1,0],LetVar 0)] (LetApp (LetFun 0) (LetFun 1)),
        lambdaToLet (LamAbs 0 (LamApp (LamVar 0) (LamAbs 1 (LamApp (LamVar 0) (LamVar 1))))) ==
          LetDef [([0,0,1],LetApp (LetVar 0) (LetVar 1)),([1,0],LetApp (LetVar 0) (LetApp (LetFun 0) (LetVar 0)))] (LetFun 1)
      ]
    ]
    

-- The main program checks and displays the results of the tests 
--
main :: IO ()
main = 
  do
    putStrLn "... Testing ..."
    simpleTestSuite simpleTests 
    putStrLn "... Completed ..."

-- process one test suite at a time
simpleTestSuite :: [[Bool]] -> IO ()
simpleTestSuite [] = 
  do
    putStr ""
simpleTestSuite (bs : bbs) =
  do
    putStrLn ("  " ++ show (length [b | b <- bs, b]) ++ " tests passed out of " ++ show (length bs))
    simpleTestSuite bbs
