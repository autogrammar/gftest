{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module GrammarContexts
  ( CtxEnv
  , ctxEnvFrom
  , equalFields
  , contexts
  , forgets
  , emptyFields
  ) where

import Data.Either (lefts)
import Data.List
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S
import EqRel
import GrammarTypes
import qualified GrammarFeat as GF
import qualified FMap as F
import qualified Mu

type SeqId = Int
type FieldIndex = Int
type ArgIndex = Int

data CtxEnv = CtxEnv
  { ceSymbols :: [Symbol]
  , ceCoercions :: [(ConcrCat, ConcrCat)]
  , ceNonEmpty :: S.Set ConcrCat
  , ceConcrSeqs :: SeqId -> [Either String (ArgIndex, FieldIndex)]
  , ceFeat :: GF.FEAT
  }

ctxEnvFrom ::
  [Symbol] ->
  [(ConcrCat, ConcrCat)] ->
  S.Set ConcrCat ->
  (SeqId -> [Either String (ArgIndex, FieldIndex)]) ->
  GF.FEAT ->
  CtxEnv
ctxEnvFrom ceSymbols ceCoercions ceNonEmpty ceConcrSeqs ceFeat =
  CtxEnv {..}

arity :: Symbol -> Int
arity = length . fst . ctyp

equalFields :: CtxEnv -> [(ConcrCat,EqRel Int)]
equalFields env = cs `zip` eqrels
 where
  eqrels = Mu.mu Top defs cs
  cs     = S.toList (ceNonEmpty env)

  defs =
    [ (c, depcats, h)
    | c <- cs
      -- fs = everything that has c as a goal category
      -- there's two possibilities:
    , let fs = -- 1) c is not a coercion: functions can have c as a goal category
               [ Right f
               | f <- ceSymbols env
               , all (`S.member` ceNonEmpty env) (fst (ctyp f))
               , c == snd (ctyp f)
               ] ++
               -- 2) c is a coercion: here's a list of (nonempty) categories c uncoerces into
               [ Left cat
               | (cat,coe) <- ceCoercions env
               , coe == c
               , cat `S.member` ceNonEmpty env
               ]

          -- all the categories c depends on
          depcats = S.toList $ S.fromList $ concat
               [ case f of
                   Right f  -> fst (ctyp f) -- 1) if c is not a coercion:
                                            -- all arg cats of the functions with c as goal cat
                   Left cat -> [cat] -- 2) if c is a coercion: just the cats that it uncoerces into
               | f <- fs
               ]

          -- Function to give to mu:
          -- computes the equivalence relation, given the eq.rels of its arguments
          h rs = foldr (/\) Top $ [ apply f eqs
                  | Right f <- fs
                  , let eqs = map (args M.!) (fst $ ctyp f)
                  ] ++
                  [ args M.! cat
                  | Left cat <- fs
                  ]
           where
            args = M.fromList (depcats `zip` rs)
    ]
   where
    apply f eqs =
      basic [ concatMap lin (ceConcrSeqs env sq)
            | sq <- seqs f
            ]
      where
        lin (Left str)    = [ str | not (null str) ]
        lin (Right (i,j)) = [ show i ++ "#" ++ show (rep (eqs !! i) j) ]

contexts :: CtxEnv -> ConcrCat -> [(ConcrCat,[Tree -> Tree])]
contexts env top =
  [ (c, map (path2context . reverse . snd) (F.toList paths))
  | (c, paths) <- cs `zip` pathss
  ]
 where
  pathss = Mu.mu F.nil defs cs
  cs     = S.toList (ceNonEmpty env)

  -- all symbols with at least one argument, and only good arguments
  goodSyms =
    [ f
    | f <- ceSymbols env
    , arity f >= 1
    , snd (ctyp f) `S.member` ceNonEmpty env
    , all (`S.member` ceNonEmpty env) (fst (ctyp f))
    ]

  -- definitions table for fixpoint iteration
  fm1 `dif` fm2 =
    [ d | d@(xs,_) <- F.toList fm1, not (fm2 `F.covers` xs) ] `ins` F.nil

  fm1 `uni` fm2 =
    F.toList fm1 `ins` fm2

  paths `ins` fm =
       foldl collect fm
     . map snd
     . sort
     $ [ (size p, p) | p <- paths ]
   where
    collect fm (str,p)
      | fm `F.covers` str = fm
      | otherwise         = F.add str p fm

    size (_,p) =
      sum [ if i == j then 1 else GF.smallest (ceFeat env) t
          | (f,i) <- p
          , let (ts,_) = ctyp f
          , (t,j) <- ts `zip` [0..]
          ]

  defs =
    [ if c == top
        then (c, [], \_ -> F.unit [0] [])
        else (c, ys, h)
    | c <- cs

      -- everything that uses c in one of the two ways:
    , let fs = -- 1) Functions that take c as the kth argument
               [ Right (f,k)
               | f <- goodSyms
               , (t,k) <- fst (ctyp f) `zip` [0..]
               , t == c
               ] ++
               -- 2) coercions that uncoerce to c
               [ Left coe
               | (cat,coe) <- ceCoercions env
               , cat == c
               , coe `S.member` ceNonEmpty env
               ]

          -- goal categories for c
          ys = S.toList $ S.fromList $
               [ case f of
                   Right (f,_) -> snd (ctyp f) -- 1) goal category of the function that uses c
                   Left coe    -> coe          -- 2)    (category of the) coercion that uncoerces to c
               | f <- fs
               ]

          -- function to give to Mu
          h ps = ([ (apply (f,k) str, (f,k):fis)
                  | Right (f,k) <- fs
                  , (str,fis) <- args M.! snd (ctyp f)
                  ] ++
                  [ q
                  | Left a <- fs
                  , q <- args M.! a
                  ]) `ins` F.nil
           where
            args = M.fromList (ys `zip` map F.toList ps)
    ]
   where                      -- fields of B that make it to the top
    apply :: (Symbol, Int) -> [Int] -> [Int] -- fields of A that make it to the top
    apply (f,k) is =
      S.toList $ S.fromList $
      [ y
      | (sq,i) <- seqs f `zip` [0..]
      , i `elem` is
      , Right (x,y) <- ceConcrSeqs env sq
      , x == k
      ]

  path2context []          x = x
  path2context ((f,i):fis) x =
    App f
    [ if j == i
        then path2context fis x
        else head (GF.featAll (ceFeat env) t)
    | (t,j) <- fst (ctyp f) `zip` [0..]
    ]

forgets :: CtxEnv -> ConcrCat -> [(ConcrCat,[Tree])]
forgets env top =
  filter (not . null . snd)
  [ (c, [ path2context (reverse p) (head (GF.featAll (ceFeat env) c))
        | (is,p) <- F.toList paths
        , length is == fields c -- all indices forgotten
        ]
    )
  | (c, paths) <- cs `zip` pathss
  ]
 where
  pathss = Mu.muDiff F.nil F.isNil dif uni defs cs
  cs     = S.toList (ceNonEmpty env)

  -- all symbols with at least one argument, and only good arguments
  goodSyms =
    [ f
    | f <- ceSymbols env
    , arity f >= 1
    , snd (ctyp f) `S.member` ceNonEmpty env
    , all (`S.member` ceNonEmpty env) (fst (ctyp f))
    ]

  fieldsTab =
    M.fromList $
    [ (b, length (seqs f))
    | f <- ceSymbols env
    , let (as,b) = ctyp f
    ]

  fields a =
    head $
    [ n
    | c <- a : [ b | (b,a') <- ceCoercions env, a' == a ]
    , Just n <- [M.lookup c fieldsTab]
    ] ++
    error (show a ++ " has no function creating it")

  -- definitions table for fixpoint iteration
  fm1 `dif` fm2 =
    [ d | d@(xs,_) <- F.toList fm1, not (fm2 `F.covers` xs) ] `ins` F.nil

  fm1 `uni` fm2 =
    F.toList fm1 `ins` fm2

  paths `ins` fm =
       foldl collect fm
     . map snd
     . sort
     $ [ (size p, p) | p <- paths ]
   where
    collect fm (str,p)
      | fm `F.covers` str = fm
      | otherwise         = F.add str p fm

    size (_,p) =
      sum [ if i == j then 1 else GF.smallest (ceFeat env) t
          | (f,i) <- p
          , let (ts,_) = ctyp f
          , (t,j) <- ts `zip` [0..]
          ]

  defs =
    [ if c == top
        then (c, [], \_ -> F.unit [] [])
        else (c, ys, h)
    | c <- cs

      -- everything that uses c in one of the two ways:
    , let fs = -- 1) Functions that take c as the kth argument
               [ Right (f,k)
               | f <- goodSyms
               , (t,k) <- fst (ctyp f) `zip` [0..]
               , t == c
               ] ++
               -- 2) coercions that uncoerce to c
               [ Left coe
               | (cat,coe) <- ceCoercions env
               , cat == c
               , coe `S.member` ceNonEmpty env
               ]

          -- goal categories for c
          ys = S.toList $ S.fromList $
               [ case f of
                   Right (f,_) -> snd (ctyp f)
                   Left coe    -> coe
               | f <- fs
               ]

          h ps = ([ (apply (f,k) str, (f,k):fis)
                  | Right (f,k) <- fs
                  , (str,fis) <- args M.! snd (ctyp f)
                  , length str < fields c
                  ] ++
                  [ q
                  | Left a <- fs
                  , q@(str,_) <- args M.! a
                  , length str < fields c
                  ]) `ins` F.nil
           where
            args = M.fromList (ys `zip` map F.toList ps)
    ]
   where
    apply :: (Symbol, Int) -> [Int] -> [Int]
    apply (f,k) is =
      [ y
      | y <- [0..fields (fst (ctyp f) !! k)-1]
      , y `S.notMember` used
      ]
     where
      used = S.fromList $
             [ y
             | (sq,i) <- seqs f `zip` [0..]
             , i `notElem` is
             , Right (x,y) <- ceConcrSeqs env sq
             , x == k
             ]

  path2context []          x = x
  path2context ((f,i):fis) x =
    App f
    [ if j == i
        then path2context fis x
        else head (GF.featAll (ceFeat env) t)
    | (t,j) <- fst (ctyp f) `zip` [0..]
    ]

--traceLength s xs = trace (s ++ ":" ++ show (length xs)) xs

emptyFields :: CtxEnv -> [(ConcrCat,S.Set Int)]
emptyFields env = cs `zip` fields
 where
  cs     = S.toList (ceNonEmpty env)
  fields = Mu.mu S.empty defs cs

  defs =
    [ (c, ys, h)
    | c <- cs
    , let fs =  -- everything that has c as a goal category
               [ Right f
               | f <- ceSymbols env
               , all (`S.member` ceNonEmpty env) (fst (ctyp f))
               , c == snd (ctyp f)
               ] ++
               -- 2) c is a coercion: here's a list of (nonempty) categories c uncoerces into
               [ Left cat
               | (cat,coe) <- ceCoercions env
               , coe == c
               , cat `S.member` ceNonEmpty env
               ]

          -- all the categories c depends on
          ys = S.toList $ S.fromList $ concat
               [ case f of
                   Right f  -> fst (ctyp f)
                   Left cat -> [cat]
               | f <- fs
               ]

          -- Function to give to mu:
          -- computes whether the field is empty, given the emptiness of its arguments.
          -- a field in C is empty, if there's some function
          --      f :: A -> B -> C
          -- and it uses only empty fields from A and B.
          -- we're only looking at a given C at a time,

          h :: [S.Set Int] -> S.Set Int
          h vs = foldr1 S.intersection $ [ apply f emptyfields
                  | Right f <- fs
                  , let emptyfields = map (args M.!) (fst $ ctyp f)
                  ] ++
                  [ args M.! cat
                  | Left cat <- fs
                  ]
           where
            args :: M.Map ConcrCat (S.Set Int) -- empty fields of each category
            args = M.fromList (ys `zip` vs)
    ]
   where
    --apply :: Symbol        -- some f :: A -> B
    --        -> [S.Set Int] -- for each argument type to f, which fields are empty
    --        -> S.Set Int   -- empty fields in B
    apply f empties =
      S.fromList
      [ i
      | (sq,i) <- seqs f `zip` [0..]
      , let isEmpty s = case s of
              Left str    -> str == ""
              Right (k,j) -> j `S.member` (empties !! k)
      , all isEmpty (ceConcrSeqs env sq)
      ]
