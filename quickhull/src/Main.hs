{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Main where
import qualified Data.Array.Accelerate as A
import qualified Data.Array.Accelerate.LLVM.Native as CPU
import Criterion
import Criterion.Main

import Quickhull
import qualified Data.ByteString as B
import qualified Data.ByteString.Internal as BI
import GHC.IsList
import Data.Int
import Foreign.ForeignPtr (ForeignPtr, castForeignPtr)
import Foreign.Storable
import Foreign.ForeignPtr (ForeignPtr, castForeignPtr, withForeignPtr)
import Foreign.Ptr

main :: IO ()
main = do
  putStrLn $ A.test @CPU.UniformScheduleFun @CPU.NativeKernel quickhull
    -- List of input files
  inputs <- mapM load ["1M_rectangle", "1M_circle", "1M_quadratic"]

  let quickhullCPU = CPU.runN quickhull

  mapM_ (testInput ("CPU", quickhullCPU)) inputs
  defaultMain [backend "CPU" quickhullCPU inputs]
  where
    backend name quickhull' inputs =
      bgroup name (Prelude.map (testcase quickhull') inputs)

    testcase quickhull' (name, points) =
      bench name $ nf quickhull' points

type Input = (String, A.Vector Point)


load :: String -> IO Input
load name = do
  putStrLn $ "Loading " ++ name
  content <- B.readFile $ "../input/" ++ name ++ ".dat"
  let (fptrw8, nw8) = BI.toForeignPtr0 content
  res <- withForeignPtr (castForeignPtr fptrw8 :: ForeignPtr Int32) $ \ptr ->
    A.fromFunctionM (A.Z A.:. (nw8 `quot` 8))
      (\(A.Z A.:. ix) -> do
        x <- peekElemOff ptr (2 * ix)
        y <- peekElemOff ptr (2 * ix + 1)
        return (fromIntegral x, fromIntegral y))
  return (name, res)

testInput :: (String, A.Vector Point -> A.Vector Point) -> Input -> IO ()
testInput (backend, f) (inputName, inputData) = do
  putStrLn $ backend ++ "/" ++ inputName
  putStrLn $ take 80 $ show $ f inputData
  putStrLn ""

chunk :: Int -> [a] -> [[a]]
chunk _ [] = []
chunk i xs = let (f, r) = splitAt i xs in f : chunk i r
