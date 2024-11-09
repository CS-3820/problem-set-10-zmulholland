module Tests where

import Data.List (partition)
import System.Exit ( exitWith, ExitCode(ExitFailure, ExitSuccess) )
import System.Environment ( getArgs )
import Test.HUnit
    ( Test,
      assertBool,
      runTestTT,
      Counts(failures, errors),
      Testable(test) )
import Text.Read (readMaybe)

import Problems10

--------------------------------------------------------------------------------

substTests1 = [ (Plus (Const 1) (Store (Plus (Const 2) (Var "x"))), "x", Const 3)
              , (Plus (Const 1) (Store (Plus (Const 2) (Var "y"))), "x", Const 3)
              , (App (Const 1) (Store (Var "x")), "x", Const 14)
              , (Plus (Const 1) (Store (Plus (Var "x") Recall)), "x", Const 3) ]

substResults1 = [Plus (Const 1) (Store (Plus (Const 2) (Const 3))),Plus (Const 1) (Store (Plus (Const 2) (Var "y"))),App (Const 1) (Store (Const 14)),Plus (Const 1) (Store (Plus (Const 3) Recall))]

substTests2 = [ (Plus (Const 1) (Catch (Plus (Const 2) (Throw (Var "x"))) "y" (Plus (Var "x") (Var "y"))), "x", Const 1)
              , (App (Const 1) (Catch (Plus (Throw (Var "x")) (Const 1)) "x" (Plus (Var "x") (Var "y"))), "x", Const 1)
              , (Catch (Plus (Store (Throw (Var "x"))) (Throw (Store (Var "x")))) "x"
                  (Catch (Plus (Var "x") (Var "y")) "y" (Plus (Var "x") (Var "y"))), "y", Const 14)
              ]

substResults2 = [Plus (Const 1) (Catch (Plus (Const 2) (Throw (Const 1))) "y" (Plus (Const 1) (Var "y"))),App (Const 1) (Catch (Plus (Throw (Const 1)) (Const 1)) "x" (Plus (Var "x") (Var "y"))),Catch (Plus (Store (Throw (Var "x"))) (Throw (Store (Var "x")))) "x" (Catch (Plus (Var "x") (Const 14)) "y" (Plus (Var "x") (Var "y")))]

substTests ts es = test [assertBool ("Expected substituting (" ++ show n ++ ") for " ++ x ++ " in (" ++ show m ++ ") to give (" ++ show expected ++ "), but got (" ++ show actual ++ ")") (expected == actual) | ((m, x, n), expected) <- zip ts es, let actual = subst x n m]

--------------------------------------------------------------------------------

evalTests1 = [(Const 1, Const 0), (Const 4, Const 12)]

evalResults1 = [[(Const 1,Const 0)],[(Const 4,Const 12)]]

evalTests2 = [ (Plus (Const 1) (Const 2), Const 0)
             , (Plus (Plus (Const 1) (Const 2)) (Const 3), Const 12)
             , (Plus (Plus (Const 1) (Const 2)) (Plus (Const (-1)) (Const 14)), Const 0)
             , (Plus (Plus (Throw (Const 1)) (Const 2)) (Plus (Const 3) (Const 4)), Const 0)
             , (Plus (Plus (Const 3) (Const 4)) (Plus (Const 3) (Throw (Const 4))), Const 0)
             , (Plus (Plus (Const 3) (Const 4)) (Plus (Plus (Const 3) (Const 4)) (Throw (Const 4))), Const 0) ]

evalResults2 = [[(Plus (Const 1) (Const 2),Const 0),(Const 3,Const 0)],[(Plus (Plus (Const 1) (Const 2)) (Const 3),Const 12),(Plus (Const 3) (Const 3),Const 12),(Const 6,Const 12)],[(Plus (Plus (Const 1) (Const 2)) (Plus (Const (-1)) (Const 14)),Const 0),(Plus (Const 3) (Plus (Const (-1)) (Const 14)),Const 0),(Plus (Const 3) (Const 13),Const 0),(Const 16,Const 0)],[(Plus (Plus (Throw (Const 1)) (Const 2)) (Plus (Const 3) (Const 4)),Const 0),(Plus (Throw (Const 1)) (Plus (Const 3) (Const 4)),Const 0),(Throw (Const 1),Const 0)],[(Plus (Plus (Const 3) (Const 4)) (Plus (Const 3) (Throw (Const 4))),Const 0),(Plus (Const 7) (Plus (Const 3) (Throw (Const 4))),Const 0),(Plus (Const 7) (Throw (Const 4)),Const 0),(Throw (Const 4),Const 0)],[(Plus (Plus (Const 3) (Const 4)) (Plus (Plus (Const 3) (Const 4)) (Throw (Const 4))),Const 0),(Plus (Const 7) (Plus (Plus (Const 3) (Const 4)) (Throw (Const 4))),Const 0),(Plus (Const 7) (Plus (Const 7) (Throw (Const 4))),Const 0),(Plus (Const 7) (Throw (Const 4)),Const 0),(Throw (Const 4),Const 0)]]

evalTests3 = [ (Lam "x" (Var "x"), Const 0)
             , (Lam "x" (Plus (Const 1) (Const 2)), Const 0)
             , (Lam "y" (Plus (Const 0) Recall), Const 12)
             , (Lam "z" (Plus (Throw (Const 0)) (Var "z")), Const 3) ]

evalResults3 = [[(Lam "x" (Var "x"),Const 0)],[(Lam "x" (Plus (Const 1) (Const 2)),Const 0)],[(Lam "y" (Plus (Const 0) Recall),Const 12)],[(Lam "z" (Plus (Throw (Const 0)) (Var "z")),Const 3)]]             

evalTests4 = [ (App (Lam "x" (Var "x")) (Const 1), Const 0)
             , (App (Lam "x" (Plus (Var "x") (Var "x"))) (App (Lam "x" (Var "x")) (Const 1)), Const 0)
             , (App (App (Lam "x" (Lam "y" (Plus (Var "x") (Var "y")))) (Const 2)) (Const 1), Const 12)
             , (App (Lam "x" (Var "x")) (Throw (Const 1)), Const 0)
             , (App (App (Lam "x" (Lam "y" (Var "x"))) (Const 1)) (Throw (Const 2)), Const 0)
             , (App (App (Lam "x" (Lam "y" (Var "x"))) (Throw (Const 1))) (Const 2), Const 0)
             , (App (App (Lam "x" (Lam "y" (Var "x"))) (Throw (Const 1))) (Throw (Const 2)), Const 0)
             , (App (Lam "x" (Throw (Var "x"))) (Const 1), Const 1)
             ]

evalResults4 = [[(App (Lam "x" (Var "x")) (Const 1),Const 0),(Const 1,Const 0)],[(App (Lam "x" (Plus (Var "x") (Var "x"))) (App (Lam "x" (Var "x")) (Const 1)),Const 0),(App (Lam "x" (Plus (Var "x") (Var "x"))) (Const 1),Const 0),(Plus (Const 1) (Const 1),Const 0),(Const 2,Const 0)],[(App (App (Lam "x" (Lam "y" (Plus (Var "x") (Var "y")))) (Const 2)) (Const 1),Const 12),(App (Lam "y" (Plus (Const 2) (Var "y"))) (Const 1),Const 12),(Plus (Const 2) (Const 1),Const 12),(Const 3,Const 12)],[(App (Lam "x" (Var "x")) (Throw (Const 1)),Const 0),(Throw (Const 1),Const 0)],[(App (App (Lam "x" (Lam "y" (Var "x"))) (Const 1)) (Throw (Const 2)),Const 0),(App (Lam "y" (Const 1)) (Throw (Const 2)),Const 0),(Throw (Const 2),Const 0)],[(App (App (Lam "x" (Lam "y" (Var "x"))) (Throw (Const 1))) (Const 2),Const 0),(App (Throw (Const 1)) (Const 2),Const 0),(Throw (Const 1),Const 0)],[(App (App (Lam "x" (Lam "y" (Var "x"))) (Throw (Const 1))) (Throw (Const 2)),Const 0),(App (Throw (Const 1)) (Throw (Const 2)),Const 0),(Throw (Const 1),Const 0)],[(App (Lam "x" (Throw (Var "x"))) (Const 1),Const 1),(Throw (Const 1),Const 1)]]

evalTests5 = [ (Store (Const 2), Const 0)
             , (Store (Plus (Const 1) (Const 2)), Const 0)
             , (Store (Plus (Store (Const 1)) (Const 2)), Const 0) 
             , (Store (Lam "x" (Store (Var "x"))), Const 12) 
             , (Store (Plus (Const 1) (Throw (Const 2))), Const 1)
             , (Store (Store (Throw (Const 3))), Const 1)
             , (Store (Throw (Store (Const 2))), Const 1) ]

evalResults5 = [[(Store (Const 2),Const 0),(Const 2,Const 2)],[(Store (Plus (Const 1) (Const 2)),Const 0),(Store (Const 3),Const 0),(Const 3,Const 3)],[(Store (Plus (Store (Const 1)) (Const 2)),Const 0),(Store (Plus (Const 1) (Const 2)),Const 1),(Store (Const 3),Const 1),(Const 3,Const 3)],[(Store (Lam "x" (Store (Var "x"))),Const 12),(Lam "x" (Store (Var "x")),Lam "x" (Store (Var "x")))],[(Store (Plus (Const 1) (Throw (Const 2))),Const 1),(Store (Throw (Const 2)),Const 1),(Throw (Const 2),Const 1)],[(Store (Store (Throw (Const 3))),Const 1),(Store (Throw (Const 3)),Const 1),(Throw (Const 3),Const 1)],[(Store (Throw (Store (Const 2))),Const 1),(Store (Throw (Const 2)),Const 2),(Throw (Const 2),Const 2)]]             

evalTests6 = [ (Recall, Const 12)
             , (Plus (Store (Const 4)) Recall, Const 0)
             , (Plus Recall (Store (Const 4)), Const 0)
             , (App (Lam "x" (App Recall (Const 1))) (Store (Lam "y" (Plus (Var "y") (Const 1)))), Const 0)
             ]             

evalResults6 = [[(Recall,Const 12),(Const 12,Const 12)],[(Plus (Store (Const 4)) Recall,Const 0),(Plus (Const 4) Recall,Const 4),(Plus (Const 4) (Const 4),Const 4),(Const 8,Const 4)],[(Plus Recall (Store (Const 4)),Const 0),(Plus (Const 0) (Store (Const 4)),Const 0),(Plus (Const 0) (Const 4),Const 4),(Const 4,Const 4)],[(App (Lam "x" (App Recall (Const 1))) (Store (Lam "y" (Plus (Var "y") (Const 1)))),Const 0),(App (Lam "x" (App Recall (Const 1))) (Lam "y" (Plus (Var "y") (Const 1))),Lam "y" (Plus (Var "y") (Const 1))),(App Recall (Const 1),Lam "y" (Plus (Var "y") (Const 1))),(App (Lam "y" (Plus (Var "y") (Const 1))) (Const 1),Lam "y" (Plus (Var "y") (Const 1))),(Plus (Const 1) (Const 1),Lam "y" (Plus (Var "y") (Const 1))),(Const 2,Lam "y" (Plus (Var "y") (Const 1)))]]             

evalTests7 = [ (Throw (Const 1), Const 0)
             , (Throw (Throw (Const 1)), Const 0) ]

evalResults7 = [[(Throw (Const 1),Const 0)],[(Throw (Throw (Const 1)),Const 0),(Throw (Const 1),Const 0)]]

evalTests8 = [ (Catch (Throw (Const 1)) "y" (Plus (Var "y") (Const 1)), Const 0)
             , (App (Lam "f" (Catch (App (Var "f") (Const 2)) "f" (App (Var "f") (Const 1))))
                    (Lam "x" (Plus (Var "x") (Const 1))), Const 12) 
             , (App (Lam "f" (Catch (App (Var "f") (Const 2)) "f" (App (Var "f") (Const 1))))
                    (Lam "x" (Throw (Lam "y" (Plus (Var "x") (Const 1))))), Const 12) 
             , (App (Lam "f" (Catch (App (Var "f") (Const 2)) "f" (App (Var "f") (Const 1))))
                    (Lam "x" (Throw (Lam "y" (Plus (Var "y") (Const 1))))), Const 12) 
             , (App (Lam "f" (Catch (App (Var "f") (Const 2)) "f" (App (Var "f") (Const 1))))
                    (Throw (Lam "y" (Plus (Var "y") (Const 1)))), Const 12) 
             ]

evalResults8 = [[(Catch (Throw (Const 1)) "y" (Plus (Var "y") (Const 1)),Const 0),(Plus (Const 1) (Const 1),Const 0),(Const 2,Const 0)],[(App (Lam "f" (Catch (App (Var "f") (Const 2)) "f" (App (Var "f") (Const 1)))) (Lam "x" (Plus (Var "x") (Const 1))),Const 12),(Catch (App (Lam "x" (Plus (Var "x") (Const 1))) (Const 2)) "f" (App (Var "f") (Const 1)),Const 12),(Catch (Plus (Const 2) (Const 1)) "f" (App (Var "f") (Const 1)),Const 12),(Catch (Const 3) "f" (App (Var "f") (Const 1)),Const 12),(Const 3,Const 12)],[(App (Lam "f" (Catch (App (Var "f") (Const 2)) "f" (App (Var "f") (Const 1)))) (Lam "x" (Throw (Lam "y" (Plus (Var "x") (Const 1))))),Const 12),(Catch (App (Lam "x" (Throw (Lam "y" (Plus (Var "x") (Const 1))))) (Const 2)) "f" (App (Var "f") (Const 1)),Const 12),(Catch (Throw (Lam "y" (Plus (Const 2) (Const 1)))) "f" (App (Var "f") (Const 1)),Const 12),(App (Lam "y" (Plus (Const 2) (Const 1))) (Const 1),Const 12),(Plus (Const 2) (Const 1),Const 12),(Const 3,Const 12)],[(App (Lam "f" (Catch (App (Var "f") (Const 2)) "f" (App (Var "f") (Const 1)))) (Lam "x" (Throw (Lam "y" (Plus (Var "y") (Const 1))))),Const 12),(Catch (App (Lam "x" (Throw (Lam "y" (Plus (Var "y") (Const 1))))) (Const 2)) "f" (App (Var "f") (Const 1)),Const 12),(Catch (Throw (Lam "y" (Plus (Var "y") (Const 1)))) "f" (App (Var "f") (Const 1)),Const 12),(App (Lam "y" (Plus (Var "y") (Const 1))) (Const 1),Const 12),(Plus (Const 1) (Const 1),Const 12),(Const 2,Const 12)],[(App (Lam "f" (Catch (App (Var "f") (Const 2)) "f" (App (Var "f") (Const 1)))) (Throw (Lam "y" (Plus (Var "y") (Const 1)))),Const 12),(Throw (Lam "y" (Plus (Var "y") (Const 1))),Const 12)]]

evalTests ts es = test [assertBool (unlines ("Evaluating" : show s : "should have given" : map show expected ++
                                             "but got" : map show actual)) (expected == actual) | (s, expected) <- zip ts es, let actual = steps s ]


--------------------------------------------------------------------------------
-- main
--------------------------------------------------------------------------------

allTests :: [(Int, Test)]
allTests = zip [1..] $ [substTests substTests1 substResults1, substTests substTests2 substResults2] ++
                       [evalTests ts es | (ts, es) <- zip [evalTests1, evalTests2, evalTests3, evalTests4, evalTests5, evalTests6, evalTests7, evalTests8]
                                                          [evalResults1, evalResults2, evalResults3, evalResults4, evalResults5, evalResults6, evalResults7, evalResults8]]

main :: IO ()
main = do
  allArgs <- getArgs
  let (makeJson, testIdxs) = partition ("json" ==) allArgs
      tests | null testIdxs = allTests
            | otherwise = pickTests (ranges testIdxs)
  
  if not (null makeJson) 
  then putStrLn (testsJson tests)
  else do results <- runTestTT (test $ map snd tests)
          if (errors results + failures results == 0)
            then
              exitWith ExitSuccess
            else
              exitWith (ExitFailure 1)

  where ranges [] = []
        ranges (s : ss)
            | Just i <- readMaybe s          = i : ranges ss
            | otherwise                      = error "Unknown ranges"
            where go []           = []
                  go (i : j : ks) = i : j : go ks
      
        pickTests (i : j : ks) = between i j ++ pickTests ks
        pickTests [i]          = [allTests !! (i - 1)]
        pickTests []           = []
      
        between i j = take (j - i + 1) (drop (i - 1) allTests)

        testsJson tests =
            unlines [ "{\"name\" : \"Problem " ++ show n ++ "\", \"setup\" : \"\", \"run\" : \"cabal run Test " ++ show n ++ "\", \"input\" : \"\", \"output\" : \"\", \"comparison\" : \"included\", \"timeout\" : 0.5, \"points\" : 1 },"
                    | (n, t) <- tests
                    ]
