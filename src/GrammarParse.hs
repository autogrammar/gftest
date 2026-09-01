{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module GrammarParse (mkTree, ParseEnv, parseEnvFrom) where

import GrammarTypes
import qualified GrammarCoercion as GC
import qualified PGF2

type SeqId = Int

data ParseEnv = ParseEnv
  { peLookup :: String -> [Symbol]
  , peCoercions :: [(ConcrCat, ConcrCat)]
  }

parseEnvFrom ::
  (String -> [Symbol]) ->
  [(ConcrCat, ConcrCat)] ->
  ParseEnv
parseEnvFrom peLookup peCoercions =
  ParseEnv {peLookup = peLookup, peCoercions = peCoercions}

mkTree :: ParseEnv -> PGF2.Expr -> Tree
mkTree env = disambTree . ambTree
 where
  ParseEnv {peLookup, peCoercions} = env
  uncoerceList = GC.uncoerceList peCoercions

  ambTree t =
    case PGF2.unApp t of
      Just (f, xs) -> App (peLookup f) [ambTree x | x <- xs]
      Nothing -> error (PGF2.showExpr [] t)

  disambTree at =
    case foldTree reduce at of
      App [x] ts -> App x [disambTree t | t <- ts]
      App _ _ts -> error "mkTree: invalid tree"

  reduce fs as =
    let red =
          [ symbol
          | symbol <- fs
          , let argTypes = uncoerceList `map` fst (ctyp symbol)
          , let goalTypes =
                  uncoerceList `map` [snd (ctyp s) | App [s] _ <- as]
          , and [intersect a r /= [] | (a, r) <- zip argTypes goalTypes]
          ]
     in case red of
          [x] -> App [x] as
          _ -> App fs as

  intersect a r = [x | x <- a, x `elem` r]
