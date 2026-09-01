{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module GrammarFeat
  ( FEAT
  , mkFEAT
  , smallest
  , featCard
  , featIth
  , featAll
  , featCardVec
  , featIthVec
  ) where

import GrammarTypes
import qualified Data.Map as M
import qualified Data.Set as S

type FEAT = [ConcrCat] -> Int -> (Integer, Integer -> [Tree])

smallest :: FEAT -> ConcrCat -> Int
smallest feat c = head [n | n <- [0 ..], featCard feat c n > 0]

featCard :: FEAT -> ConcrCat -> Int -> Integer
featCard feat c n = featCardVec feat [c] n

featIth :: FEAT -> ConcrCat -> Int -> Integer -> Tree
featIth feat c n i = head (featIthVec feat [c] n i)

featAll :: FEAT -> ConcrCat -> [Tree]
featAll feat c = [featIth feat c n i | n <- [0 ..], i <- [0 .. featCard feat c n - 1]]

featCardVec :: FEAT -> [ConcrCat] -> Int -> Integer
featCardVec feat cs n = fst (feat cs n)

featIthVec :: FEAT -> [ConcrCat] -> Int -> Integer -> [Tree]
featIthVec feat cs n i = snd (feat cs n) i

mkFEAT :: [Symbol] -> [(ConcrCat, ConcrCat)] -> FEAT
mkFEAT symbols coercions = catList
 where
  catList' :: FEAT
  catList' [] 0 = (1, \0 -> [])
  catList' [] _ = (0, error "indexing in an empty sequence")

  catList' [c] s =
    parts $
      [ (n, \i -> [App f (h i)])
      | s > 0
      , f <- symbols
      , let (xs, y) = ctyp f
      , y == c
      , let (n, h) = catList xs (s - 1)
      ]
        ++ [ catList [x] s
           | s > 0
           , (x, y) <- coercions
           , y == c
           ]

  catList' (c : cs) s =
    parts
      [ (nx * nxs, \i -> hx (i `mod` nx) ++ hxs (i `div` nx))
      | k <- [0 .. s]
      , let (nx, hx) = catList [c] k
            (nxs, hxs) = catList cs (s - k)
      ]

  catList :: FEAT
  catList = memoList (memoNat . catList')
   where
    cats =
      S.toList $
        S.fromList $
          [x | f <- symbols, let (xs, y) = ctyp f, x <- y : xs]
            ++ [z | (x, y) <- coercions, z <- [x, y]]

    memoList f = \cs -> case cs of
      [] -> fNil
      a : as -> fCons a as
     where
      fNil = f []
      fCons = (tab M.!)
      tab = M.fromList [(c, memoList (f . (c :))) | c <- cats]

    memoNat f = (tab !!)
     where
      tab = [f i | i <- [0 ..]]

  parts [] = (0, error "indexing outside of a sequence")
  parts ((n, h) : nhs) = (n + n', \i -> if i < n then h i else h' (i - n))
   where
    (n', h') = parts nhs
