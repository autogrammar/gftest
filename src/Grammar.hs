{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Grammar
    ( Grammar(..), readGrammar
    , module GrammarTypes
    , AmbTree

    -- Categories, coercions
    , ccats, ccatOf, arity
    , coerces, uncoerce
    , uncoerceAbsCat, mkCC

    -- Testing and comparison
    , testTree, testFun
    , compareTree, Comparison(..)
    , treesUsingFun

    -- Contexts
    , contextsFor, dummyHole

    -- FEAT
    , featIth, featCard

    -- Fields
    , forgets, reachableFieldsFromTop
    , emptyFields, equalFields, fieldNames

    -- misc
    , showConcrFun, subTree, flatten
    , diffCats, hasConcrString
) where

import Data.Either ( lefts )
import Data.List
import qualified Data.Map as M
import Data.Maybe
import Data.Char
import qualified Data.Set as S
import qualified Mu
import qualified FMap as F
import qualified Data.Tree as T
import EqRel
import GrammarTypes
import qualified GrammarFeat as GF
import qualified GrammarCoercion as GCo
import qualified GrammarParse as GP
import qualified GrammarReachable as GR
import qualified GrammarContexts as GCtx
import GrammarTesting
  ( diffCats, hasConcrString, Comparison(..), dummyHole
  , compareTree, testFun, testTree, treesUsingFun
  )
import GrammarBuild (readGrammar, toGrammar)

import GHC.Exts ( the )
import Debug.Trace

import qualified PGF2
import qualified PGF2.Internal as I

type AmbTree = RoseTree [Symbol]

arity :: Symbol -> Int
arity = length . fst . ctyp

hole :: ConcrCat -> Symbol
hole c = Symbol (show c) [] ([], "") ([],c)

showConcrFun :: Grammar -> Symbol -> String
showConcrFun gr detCN = show detCN ++ " : " ++ args ++ show np_209
 where
  (dets_cns,np_209) = ctyp detCN
  args = concatMap (\x -> show x ++ " → ") dets_cns

type SeqId = Int
type FieldIndex = Int
type ArgIndex = Int
type FieldName = String

data Grammar
  = Grammar
  {
    concrLang    :: Lang
  , parse        :: String -> [Tree]
  , readTree     :: String -> Tree
  , linearize    :: Tree -> String
  , tabularLin   :: Tree ->  [(String,String)]
  , fields       :: M.Map Cat (M.Map FieldIndex FieldName)
  , concrCats    :: [(PGF2.Cat,I.FId,I.FId,[String])]
  , coercions    :: [(ConcrCat,ConcrCat)]
  , contextsTab  :: M.Map ConcrCat (M.Map ConcrCat [Tree -> Tree])
  , startCat     :: Cat
  , symbols      :: [Symbol]
  , lookupSymbol :: String -> [Symbol]
  , functionsByCat :: Cat -> [Symbol]
  , concrSeqs    :: SeqId -> [Either String (ArgIndex,FieldIndex)]
  , feat         :: GF.FEAT
  , nonEmptyCats :: S.Set ConcrCat
  , allCats      :: [ConcrCat]
  }

fieldNames :: Grammar -> Cat -> [FieldName]
fieldNames gr c = M.elems $ fields gr M.! c

reachEnv :: Grammar -> GR.ReachEnv
reachEnv gr =
  GR.reachEnvFrom
    (symbols gr)
    (coercions gr)
    (nonEmptyCats gr)
    (concrSeqs gr)

mkCC gr fid = CC ccat fid
 where ccat = case [ cat | (cat,bg,end,_) <- concrCats gr
                         , fid `elem` [bg..end] ] of
                [] -> Nothing -- means it's coercion
                xs -> Just $ the xs

-- parsing and reading trees
mkTree :: Grammar -> PGF2.Expr -> Tree
mkTree gr =
  GP.mkTree (GP.parseEnvFrom (lookupSymbol gr) (coercions gr))

-- categories and coercions
ccats :: Grammar -> Cat -> [ConcrCat]
ccats gr = GCo.ccatsFor (nonEmptyCats gr)

uncoerceAbsCat :: Grammar -> ConcrCat -> Cat
uncoerceAbsCat gr = GCo.uncoerceAbsCatFor (coercions gr)

uncoerce :: Grammar -> ConcrCat -> [ConcrCat]
uncoerce gr = GCo.uncoerceList (coercions gr)

coerces :: Grammar -> ConcrCat -> ConcrCat -> Bool
coerces gr coe cat = GCo.coercesList (coercions gr) coe cat

lookupAll :: (Eq a) => [(b,a)] -> a -> [b]
lookupAll = GCo.lookupAll

singleton [x] = True
singleton _   = False

--------------------------------------------------------------------------------
-- compute categories reachable from S

reachableCatsFromTop :: Grammar -> ConcrCat -> [ConcrCat]
reachableCatsFromTop gr = GR.reachableCatsFromTop (reachEnv gr)

reachableFieldsFromTop :: Grammar -> ConcrCat -> [(ConcrCat,S.Set Int)]
reachableFieldsFromTop gr = GR.reachableFieldsFromTop (reachEnv gr)

ctxEnv :: Grammar -> GCtx.CtxEnv
ctxEnv gr =
  GCtx.ctxEnvFrom
    (symbols gr)
    (coercions gr)
    (nonEmptyCats gr)
    (concrSeqs gr)
    (feat gr)

contextsFor :: Grammar -> ConcrCat -> ConcrCat -> [Tree -> Tree]
contextsFor gr top hole = [] `fromMaybe` M.lookup hole (contextsTab gr M.! top)

equalFields :: Grammar -> [(ConcrCat,EqRel Int)]
equalFields gr = GCtx.equalFields (ctxEnv gr)

forgets :: Grammar -> ConcrCat -> [(ConcrCat,[Tree])]
forgets gr = GCtx.forgets (ctxEnv gr)

emptyFields :: Grammar -> [(ConcrCat,S.Set Int)]
emptyFields gr = GCtx.emptyFields (ctxEnv gr)

--------------------------------------------------------------------------------
-- FEAT-style generator (see GrammarFeat)

smallest :: Grammar -> ConcrCat -> Int
smallest gr = GF.smallest (feat gr)

featCard :: Grammar -> ConcrCat -> Int -> Integer
featCard gr = GF.featCard (feat gr)

featIth :: Grammar -> ConcrCat -> Int -> Integer -> Tree
featIth gr = GF.featIth (feat gr)

featAll :: Grammar -> ConcrCat -> [Tree]
featAll gr = GF.featAll (feat gr)

featCardVec :: Grammar -> [ConcrCat] -> Int -> Integer
featCardVec gr = GF.featCardVec (feat gr)

featIthVec :: Grammar -> [ConcrCat] -> Int -> Integer -> [Tree]
featIthVec gr = GF.featIthVec (feat gr)

