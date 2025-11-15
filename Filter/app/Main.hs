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


-- Generate a random array of n Ints in [0,maxVal)
randomArray :: Int -> Int -> P.IO (Vector Int)
randomArray n maxVal = do
    gen <- newStdGen
    let xs = P.take n $ randomRs (0, maxVal-1) gen
    P.return $ fromList (Z :. n) xs

main :: P.IO ()
main = do
    let n = 50000000  -- size of array
        maxVal = 1000 -- maximum value of elements
    -- P.putStrLn $ test @UniformScheduleFun @NativeKernel $ filter' (\x -> x `mod` 2 == 0)
    -- Generate random input
    input <- randomArray n maxVal

    -- Precompile Accelerate function
    let runFilter = runN (filter' (\x -> x `mod` 2 == 0))
    runFilter `deepseq` P.putStrLn "JIT compiled boundsSafeFilter"

    -- Benchmark
    defaultMain
      [ bench ("filter even random") $ nf runFilter input ]

