{-# LANGUAGE LambdaCase #-}
module Main where

import           System.Exit (exitSuccess,exitFailure)
import           System.IO (hFlush,stdout)
import           System.Environment (getArgs)
import qualified CO4.Example.Binary
import qualified CO4.Example.Nat
import qualified CO4.Example.Prelude
import qualified CO4.Example.Simple
import qualified CO4.Example.LoopSrs
import qualified CO4.Example.LoopTrsToyama

main :: IO ()
main = do 
  getArgs >>= \case
    ["binary"]   -> binary 143
    ["binary",n] -> binary $ read n
    ["nat"]      -> nat 143
    ["nat",n]    -> nat $ read n
    ["prelude"]  -> prelude
    ["simple"]   -> simple
    ["loop-srs"] -> loopSrs
    ["loop-trs"] -> loopTrs
    _            -> all
  exitSuccess

  where
    binary  = simpleTest "CO4.Example.Binary"  . CO4.Example.Binary.result
    nat     = simpleTest "CO4.Example.Nat"     . CO4.Example.Nat.result
    prelude = simpleTest "CO4.Example.Prelude" $ CO4.Example.Prelude.result
    simple  = simpleTest "CO4.Example.Simple"  $ CO4.Example.Simple.result
    loopSrs = do simpleTest "CO4.Example.Loop: gebhardt-03"  
                  $ CO4.Example.LoopSrs.solve 16 16 "CO4/Example/LoopSrs/gebhardt-03.xml"
                 simpleTest "CO4.Example.Loop: gebhardt-08"  
                  $ CO4.Example.LoopSrs.solve 16 16 "CO4/Example/LoopSrs/gebhardt-08.xml"
                 simpleTest "CO4.Example.Loop: zantema_z042"  
                  $ CO4.Example.LoopSrs.solve 16 16 "CO4/Example/LoopSrs/zantema_z042.xml"
                 simpleTest "CO4.Example.Loop: zantema_loop1"  
                  $ CO4.Example.LoopSrs.solve 16 16 "CO4/Example/LoopSrs/zantema_loop1.xml"

    loopTrs = simpleTest "CO4.Example.Loop: toyama" $ CO4.Example.LoopTrsToyama.result

    all = binary 143 >> nat 143 >> prelude >> simple >> loopSrs >> loopTrs

simpleTest :: String -> IO (Maybe a) -> IO ()
simpleTest name action = do
  putStrLn $ concat [ "## ", name, " ", replicate (70 - length name) '#' ]
  hFlush stdout
  action >>= \case
    Nothing -> do putStrLn $ name ++ " does not return a result. Aborting test ..."
                  exitFailure
    Just _  -> return ()
