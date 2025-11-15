module TestUtils where
import Data.List (isPrefixOf)

findMarkedLines :: String -> [String]
findMarkedLines input =
  filter (isPrefixOf "|@|") (lines input)