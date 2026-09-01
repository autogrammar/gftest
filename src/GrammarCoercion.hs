{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module GrammarCoercion
  ( lookupAll
  , ccatsFor
  , uncoerceAbsCatFor
  , uncoerceList
  , coercesList
  ) where

import GrammarTypes
import GHC.Exts ( the )
import qualified Data.Set as S

lookupAll :: (Eq a) => [(b, a)] -> a -> [b]
lookupAll kvs key = [v | (v, k) <- kvs, k == key]

ccatsFor :: S.Set ConcrCat -> Cat -> [ConcrCat]
ccatsFor nonEmpty utt =
  [cc | cc@(CC (Just cat) _) <- S.toList nonEmpty, cat == utt]

uncoerceAbsCatFor :: [(ConcrCat, ConcrCat)] -> ConcrCat -> Cat
uncoerceAbsCatFor coercions c = case c of
  CC (Just cat) _ -> cat
  CC Nothing _ -> the [uncoerceAbsCatFor coercions x | x <- uncoerceList coercions c]

uncoerceList :: [(ConcrCat, ConcrCat)] -> ConcrCat -> [ConcrCat]
uncoerceList coercions c = case c of
  CC Nothing _ -> lookupAll coercions c
  _ -> [c]

coercesList :: [(ConcrCat, ConcrCat)] -> ConcrCat -> ConcrCat -> Bool
coercesList coercions coe cat = (cat, coe) `elem` coercions
