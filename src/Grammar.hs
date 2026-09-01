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

--------------------------------------------------------------------------------
-- grammar

readGrammar :: Lang -> FilePath -> IO Grammar
readGrammar lang file =
  do pgf <- PGF2.readPGF file
     return (toGrammar pgf lang)

toGrammar :: PGF2.PGF -> Lang -> Grammar
toGrammar pgf langName =
  let gr =
        Grammar
        { concrLang = lname

        , parse = \s ->
            case PGF2.parse lang (PGF2.startCat pgf) s of
              PGF2.ParseOk es_fs -> map (mkTree gr.fst) es_fs
              PGF2.ParseFailed i s -> error s
              PGF2.ParseIncomplete -> error "Incomplete parse"

        , readTree = \s ->
            case PGF2.readExpr s of
              Just t  -> mkTree gr t
              Nothing -> error "readTree: no parse"

        , linearize = \t ->
            PGF2.linearize lang (mkExpr t)

        , tabularLin = \t ->
            PGF2.tabularLinearize lang (mkExpr t)

        , fields = M.fromList $
            [ (cat, M.fromList
                      [ (i, fn)
                      | f <- functionsByCat gr cat
                      , let (_,goalcat@(CC _ fid)) = ctyp f
                      , goalcat `S.member` nonEmptyCats gr
                      , let t:_ = GF.featAll (feat gr) goalcat
                      , (i, (fn,_) ) <- [0..(length $ seqs f)-1] `zip` tabularLin gr t
                      ]
              )
            | cat <- PGF2.categories pgf
            ]

        , startCat =
            mkCat (PGF2.startCat pgf)

        , concrCats =
            I.concrCategories lang

        , symbols =
            [ Symbol {
              name = nm,
              seqs = sqs,
              ctyp = (argsCC, goalCC),
              typ = (map (uncoerceAbsCat gr) argsCC, goalcat)
            }
            | (goalcat,bg,end,_) <- I.concrCategories lang
            , goalfid <- [bg..end]
            , I.PApply funId pargs <- I.concrProductions lang goalfid
            , let goalCC = CC (Just goalcat) goalfid
            , let argsCC = [ mkCC argfid | I.PArg _ argfid <- pargs ]
            , let (nm,sqs) = I.concrFunction lang funId ]

        , lookupSymbol = lookupAll (symb2table `map` symbols gr)

        , functionsByCat = \c ->
            [ symb
            | symb <- symbols gr
            , snd (typ symb) == c
            , snd (ctyp symb) `S.member` nonEmptyCats gr ]

        , coercions =
            [ ( mkCC cfid, CC Nothing afid )
            | afid <- [0..I.concrTotalCats lang]
            , I.PCoerce cfid <- I.concrProductions lang afid ]

        , contextsTab =
            M.fromList
            [ (top, M.fromList (GCtx.contexts (ctxEnv gr) top))
            | top <- allCats gr ]

        , concrSeqs =
            map cseq2Either . I.concrSequence lang

        , feat =
            GF.mkFEAT (symbols gr) (coercions gr)

        , allCats = S.toList $ S.fromList $
            [ a | f <- symbols gr, let (args,goal) = ctyp f
            , a <- goal:args
            ] ++
            [ c | (cat,coe) <- coercions gr
            , c <- [coe,cat]
            ]
        , nonEmptyCats = S.fromList
            [ c
            | let -- all functions, organized by result type
                  funs = M.fromListWith (++) $
                    [ (cat,[Right f])
                    | f <- symbols gr
                    , let (_,cat) = ctyp f
                    ] ++
                    [ (coe,[Left cat])
                    | (cat,coe) <- coercions gr
                    ]

                  -- all categories, with their dependencies
                  defs =
                    [ if or [ arity f == 0 | Right f <- fs ]
                        then (c, [], \_ -> True) -- has a word
                        else (c, ys, h)          -- no word
                    | c <- allCats gr
                    , let -- relevant functions for c
                          fs = fromMaybe [] (M.lookup c funs)

                          -- categories we depend on
                          ys = S.toList $ S.fromList $
                               [ cat | Right f <- fs, cat <- fst (ctyp f) ] ++
                               [ cat | Left cat <- fs ]

                          -- compute if we're empty, given the emptiness of others
                          h bs = or $
                            [ and [ tab M.! a | a <- args ]
                            | Right f <- fs
                            , let (args,_) = ctyp f
                            ] ++
                            [ tab M.! cat
                            | Left cat <- fs
                            ]
                           where
                            tab = M.fromList (ys `zip` bs)
                    ]
            , (c,True) <- allCats gr `zip` Mu.mu False defs (allCats gr)
            ]



        }
   in gr
 where
  -- language
  (lang,lname) = case M.lookup langName (PGF2.languages pgf) of
           Just la -> (la,langName)
           Nothing -> let (defName,defGr) = head $ M.assocs $ PGF2.languages pgf
                          msg = "no grammar found with name " ++ langName ++
                                ", using " ++ defName
                      in trace msg (defGr,defName)

  -- categories and expressions
  mkCat tp = cat where (_, cat, _) = PGF2.unType tp

  mkExpr (App n []) | not (null s) && all isDigit s =
    PGF2.mkInt (read s)
   where
    s = show n

  mkExpr (App f xs) =
    PGF2.mkApp (name f) [ mkExpr x | x <- xs ]

  mkCC fid = CC ccat fid
   where ccat = case [ cat | (cat,bg,end,_) <- I.concrCategories lang
                           , fid `elem` [bg..end] ] of
                  [] -> Nothing -- means it's coercion
                  xs -> Just $ the xs

  -- misc
  symb2table s = (s, name s)

  cseq2Either (I.SymKS tok)  = Left tok
  cseq2Either (I.SymCat x y) = Right (x,y)
  cseq2Either x              = Left (show x)


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

