{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use even" #-}
{-# HLINT ignore "Use lambda-case" #-}
module Main (main) where

import Data.Array.Accelerate
import Data.Array.Accelerate.LLVM.Native
import qualified Prelude as P
import Control.DeepSeq
import Criterion.Main
import System.Random


sieve :: Acc (Scalar Int) -> Acc (Vector Int)
sieve c = 
  let c' = the c
      a = generate (lift $ Z :. (c' - 1)) (\i -> unindex1 i + 2)
      (T2 _ res) = awhile (\(T2 n arr) -> unit $ the n < unindex1 (shape arr))
                          (\(T2 n arr) -> 
                            let 
                              val = arr ! index1 (the n)
                              arr' = filter' (\x -> (x `mod` val /= 0) || (x == val)) arr
                              in T2 (unit $ the n + 1) arr')
                          (T2 (unit $ lift (0 :: Int)) a)
      in res

filter' :: (Exp Int -> Exp Bool) -> Acc (Vector Int) -> Acc (Vector Int)
filter' guard arr = let (T2 res _) = filter guard arr
              in res

main :: P.IO ()
main = do
  -- Precompile the Accelerate function
  let runSieve = CPU.runN sieve
  P.putStrLn $ test @UniformScheduleFun @NativeKernel $ sieve

  -- Force JIT compilation
  runSieve `deepseq` P.putStrLn "JIT compiled sieve."

  -- Input sizes to benchmark
  let sizes = [50000, 75000, 100000] :: [Int]

  -- Create benchmarks for each input size
  let benches = 
        [ bench ("sieve " P.++ show n) $ nf runSieve (fromList Z [n :: Int])
        | n <- sizes
        ]

  defaultMain benches


