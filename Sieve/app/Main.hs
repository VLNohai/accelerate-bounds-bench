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
filter' guard arr =
    let flags   = map (\x -> boolToInt $ guard x) arr
        (T2 scanned n) = scanl' (+) 0 flags
        permuted = permuteUnique
            (fill (shape arr) 0)
            (\ix ->
                let f = flags ! ix
                in cond (f == 1)
                        (Just_ $ index1 (scanned ! ix))
                        (lift Nothing_)) arr
        in backpermute (index1 (the n)) P.id permuted

main :: P.IO ()
main = do
  -- Precompile the Accelerate function
  let runSieve = runN sieve

  -- P.putStrLn $ test @UniformScheduleFun @NativeKernel $ sieve

  -- Force the function to be fully compiled before benchmarking
  runSieve `deepseq` P.putStrLn "JIT compiled sieve."

  let input = fromList Z [100000 :: Int]

  defaultMain [ bench "sieve 100000" $ nf runSieve input ]