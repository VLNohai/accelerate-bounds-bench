{-# LANGUAGE TypeApplications #-}
module Main (main) where

import Data.Array.Accelerate
import Data.Array.Accelerate.LLVM.Native
import Data.Array.Accelerate.Data.Bits
import Data.Array.Accelerate.Unsafe
import qualified Prelude

import qualified Control.Concurrent

main :: Prelude.IO ()
main = do
  Prelude.putStrLn $ test @UniformScheduleFun @NativeKernel histogram
  Prelude.print $ run histogram $ fromList (Z :. 17) [1,2,3,4,3,3,2,5,4,3,2,9,2,2,2,3,4]

histogram :: Acc (Vector Int) -> Acc (Vector Int)
histogram xs = permute (+) zeros (\ix -> Just_ (I1 (xs ! ix))) ones
  where
    zeros = fill (constant (Z :. 10)) 0
    ones  = fill (shape xs) 1