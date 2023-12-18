module Main (main) where

import Lib(roundTripTreeVec, roundTripVecTree)
import Test.QuickCheck

main :: IO ()
main = do 
  print "Quickchecking vecToTreeToVec is identity"
  quickCheck (withMaxSuccess 10000 roundTripTreeVec)
  print "Quickchecking treeToVecToTree is identity"
  quickCheck (withMaxSuccess 10000 roundTripVecTree)
