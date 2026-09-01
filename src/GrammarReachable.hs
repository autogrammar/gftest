{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module GrammarReachable
  ( ReachEnv
  , reachEnvFrom
  , reachableCatsFromTop
  , reachableFieldsFromTop
  ) where

import GrammarTypes
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Mu

type SeqId = Int
type ArgIndex = Int
type FieldIndex = Int

data ReachEnv = ReachEnv
  { reSymbols :: [Symbol]
  , reCoercions :: [(ConcrCat, ConcrCat)]
  , reNonEmpty :: S.Set ConcrCat
  , reConcrSeqs :: SeqId -> [Either String (ArgIndex, FieldIndex)]
  }

reachEnvFrom ::
  [Symbol] ->
  [(ConcrCat, ConcrCat)] ->
  S.Set ConcrCat ->
  (SeqId -> [Either String (ArgIndex, FieldIndex)]) ->
  ReachEnv
reachEnvFrom reSymbols reCoercions reNonEmpty reConcrSeqs =
  ReachEnv {reSymbols, reCoercions, reNonEmpty, reConcrSeqs}

reachableCatsFromTop :: ReachEnv -> ConcrCat -> [ConcrCat]
reachableCatsFromTop env top =
  [c | (c, True) <- cs `zip` rs]
 where
  ReachEnv {reSymbols, reCoercions, reNonEmpty} = env
  rs = Mu.mu False defs cs
  cs = S.toList reNonEmpty
  defs =
    [ if c == top
        then (c, [], \_ -> True)
        else (c, ys, or)
    | c <- cs
    , let ys =
            S.toList $
              S.fromList $
                [ b
                | f <- reSymbols
                , let (as, b) = ctyp f
                , all (`S.member` reNonEmpty) as
                , c `elem` as
                ]
                  ++ [ b
                     | (a, b) <- reCoercions
                     , a == c
                     , b `S.member` reNonEmpty
                     ]
    ]

reachableFieldsFromTop :: ReachEnv -> ConcrCat -> [(ConcrCat, S.Set Int)]
reachableFieldsFromTop env top = cs `zip` rs
 where
  ReachEnv {reSymbols, reCoercions, reNonEmpty, reConcrSeqs} = env
  rs = Mu.mu S.empty defs cs
  cs = S.toList reNonEmpty
  defs =
    [ if c == top
        then (c, [], \_ -> S.fromList [0])
        else (c, ys, h)
    | c <- cs
    , let fs =
            [ Right (f, k)
            | f <- reSymbols
            , let (as, _) = ctyp f
            , all (`S.member` reNonEmpty) as
            , (a, k) <- as `zip` [0 ..]
            , c == a
            ]
              ++ [ Left b
                 | (a, b) <- reCoercions
                 , a == c
                 , b `S.member` reNonEmpty
                 ]
          ys =
            S.toList $
              S.fromList
                [ case entry of
                    Right (f, _) -> snd (ctyp f)
                    Left b -> b
                | entry <- fs
                ]
          h rs' =
            S.unions
              [ case entry of
                  Right (f, k) -> apply (f, k) (args M.! snd (ctyp f))
                  Left b -> args M.! b
              | entry <- fs
              ]
           where
            args = M.fromList (ys `zip` rs')
    ]
  apply (f, k) r =
    S.fromList
      [ j
      | (sq, i) <- seqs f `zip` [0 ..]
      , i `S.member` r
      , Right (k', j) <- reConcrSeqs sq
      , k' == k
      ]
