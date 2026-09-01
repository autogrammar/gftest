{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module GrammarTypes
  ( Name, Lang, Cat
  , ConcrCat(..), ccatOf
  , Tree, RoseTree, top, Symbol(..)
  , showTree, subTree, flatten, foldTree
  ) where

import Data.List ( concatMap )
import Data.Maybe ( listToMaybe, mapMaybe )
import qualified PGF2
import qualified PGF2.Internal as I

type Name = String
type Lang = String
type Cat = PGF2.Cat

data ConcrCat = CC (Maybe Cat) I.FId
  deriving ( Eq )

instance Show ConcrCat where
  show (CC (Just cat) fid) = cat ++ "_" ++ show fid
  show (CC Nothing    fid) = "_" ++ show fid

instance Ord ConcrCat where
  (CC _ fid1) `compare` (CC _ fid2) = fid1 `compare` fid2

data RoseTree a
  = App { top :: a, args :: [RoseTree a] }
 deriving ( Eq, Ord )

foldTree :: (a -> [b] -> b) -> RoseTree a -> b
foldTree f = go where
    go (App x ts) = f x (map go ts)

flatten :: RoseTree a -> [a]
flatten (App tp as) = tp : concatMap flatten as

type Tree = RoseTree Symbol

data Symbol
  = Symbol
  { name :: Name
  , seqs :: [Int]
  , typ  :: ([Cat], Cat)
  , ctyp :: ([ConcrCat],ConcrCat)
  }
 deriving ( Eq, Ord )

instance Show Symbol where
  show = name

ccatOf :: Tree -> ConcrCat
ccatOf (App tp _) = snd (ctyp tp)

instance Show Tree where
  show = showTree

showTree :: Tree -> String
showTree (App a []) = show a
showTree (App f xs) = unwords (show f : map showTreeArg xs)
  where showTreeArg (App a []) = show a
        showTreeArg t = "(" ++ showTree t ++ ")"

subTree :: Symbol -> Tree -> Maybe Tree
subTree symb t@(App tp tr)
  | symb==tp  = Just t
  | otherwise = listToMaybe $ mapMaybe (subTree symb) tr
