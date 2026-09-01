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
import qualified GrammarCoercion as GC
import qualified GrammarParse as GP
import qualified GrammarReachable as GR
import qualified GrammarContexts as GC

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
            [ (top, M.fromList (GC.contexts (ctxEnv gr) top))
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
ccats gr = GC.ccatsFor (nonEmptyCats gr)

uncoerceAbsCat :: Grammar -> ConcrCat -> Cat
uncoerceAbsCat gr = GC.uncoerceAbsCatFor (coercions gr)

uncoerce :: Grammar -> ConcrCat -> [ConcrCat]
uncoerce gr = GC.uncoerceList (coercions gr)

coerces :: Grammar -> ConcrCat -> ConcrCat -> Bool
coerces gr coe cat = GC.coercesList (coercions gr) coe cat

lookupAll :: (Eq a) => [(b,a)] -> a -> [b]
lookupAll = GC.lookupAll

singleton [x] = True
singleton _   = False

--------------------------------------------------------------------------------
-- compute categories reachable from S

reachableCatsFromTop :: Grammar -> ConcrCat -> [ConcrCat]
reachableCatsFromTop gr = GR.reachableCatsFromTop (reachEnv gr)

reachableFieldsFromTop :: Grammar -> ConcrCat -> [(ConcrCat,S.Set Int)]
reachableFieldsFromTop gr = GR.reachableFieldsFromTop (reachEnv gr)

ctxEnv :: Grammar -> GC.CtxEnv
ctxEnv gr =
  GC.ctxEnvFrom
    (symbols gr)
    (coercions gr)
    (nonEmptyCats gr)
    (concrSeqs gr)
    (feat gr)

contextsFor :: Grammar -> ConcrCat -> ConcrCat -> [Tree -> Tree]
contextsFor gr top hole = [] `fromMaybe` M.lookup hole (contextsTab gr M.! top)

equalFields :: Grammar -> [(ConcrCat,EqRel Int)]
equalFields gr = GC.equalFields (ctxEnv gr)

forgets :: Grammar -> ConcrCat -> [(ConcrCat,[Tree])]
forgets gr = GC.forgets (ctxEnv gr)

emptyFields :: Grammar -> [(ConcrCat,S.Set Int)]
emptyFields gr = GC.emptyFields (ctxEnv gr)

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

--------------------------------------------------------------------------------
-- Functions used in Main

-- compare two grammars
diffCats :: Grammar -> Grammar -> [(Cat,[Int],[String],[String])]
diffCats gr1 gr2 =
  [ (acat1,[difFid c1, difFid c2],labels1  \\ labels2,labels2 \\ labels1)
    | c1@(acat1,_i1,_j2,labels1) <- concrCats gr1
    , c2@(acat2,_i2,_j2,labels2) <- concrCats gr2
    , difFid c1 /= difFid c2 -- different amount of concrete categories
      || labels1 /= labels2 -- or the labels are different
    , acat1==acat2 ]

 where
  difFid (_,i,j,_) = 1 + (j-i)


-- return a list of symbols that have a specified string, e.g. "it" in English
-- grammar appears in functions CleftAdv, CleftNP, ImpersCl, DefArt, it_Pron
hasConcrString :: Grammar -> String -> [Symbol]
hasConcrString gr str =
  [ symb
  | symb <- symbols gr
  , str `elem` concatMap (lefts . concrSeqs gr) (seqs symb) ]

-- nice printouts
type Context = String
type LinTree = ((Lang,Context),(Lang,String),(Lang,String),(Lang,String))
data Comparison = Comparison { funTree :: String, linTree :: [LinTree] }

instance Show Comparison where
  show c = unlines $ funTree c : map showLinTree (linTree c)

dummyCCat = CC Nothing 99999999
dummyHole = App (Symbol "∅" [] ([], "") ([], dummyCCat)) []

showLinTree :: LinTree -> String
showLinTree ((an,hl),(l1,t1),(l2,t2),(_l,[])) = unlines ["", an++hl, l1++t1, l2++t2]
showLinTree ((an,hl),(l1,t1),(l2,t2),(l3,t3)) = unlines ["", an++hl, l1++t1, l2++t2, l3++t3]

compareTree :: Bool -> Grammar -> Grammar -> [Grammar] -> Cat -> Tree -> Comparison
compareTree debug gr oldgr transgr startcat t =
 let f = if debug
          then trace (show t)
          else id
  in f $ Comparison {
            funTree = "* " ++ show t
          , linTree = [ ( ("** ",hl),
                          (langName gr,newLin),
                          (langName oldgr, oldLin),
                          transLin )
                      | ctx <- ctxs
                      , let hl = show (ctx dummyHole)
                      , let newLin = linearize gr (ctx t)
                      , let oldLin = linearize oldgr (ctx t)
                      , let transLin = case transgr of
                                        []  -> ("","")
                                        g:_ -> (langName g, linearize g (ctx t))
                      , newLin /= oldLin
                      ] }
 where
  w    = top t
  c    = snd (ctyp w)
  cs   = c:[ coe
           | (cat,coe) <- coercions gr
           , c == cat ]
  ctxs = concat
         [ contextsFor gr sc cat
         | sc <- ccats gr startcat
         , cat <- cs ]
  langName gr = concrLang gr ++ "> "

type Result = String

testFun :: Bool -> Grammar -> [Grammar] -> Cat -> Name -> Result
testFun debug gr trans startcat funname =
 let test = testTree debug gr trans
  in unlines [ test t n cs
             | (n,(t,cs)) <- zip [1..] testcase_ctxs ]

 where
  testcase_ctxs = M.toList $ M.fromListWith (++) $ uniqueTCs++commonTCs

  uniqueTCs = [ (testcase,uniqueCtxs)
   | (cat,(testcase,ctxs)) <- cat_testcase_ctxs
   , let uniqueCtxs = deleteFirstsBy applyHole ctxs (commonCtxs cat)
   , not $ null uniqueCtxs
   ]
  commonTCs = [ (App newTop subtrees,ctxs)
   | (coe,cats,ctxs) <- coercion_goalcats_commonCtxs
   , let testcases_ctxs = catMaybes [ lookup cat cat_testcase_ctxs
                                    | cat <- cats ]
   , not $ null testcases_ctxs
   , let fstLen (a,_) (b,_) = length (flatten a) `compare` length (flatten b)
   , let (App tp subtrees,_) = -- pick smallest test case to be the representative
           minimumBy fstLen testcases_ctxs
   , let newTop = -- debug: put coerced contexts under a separate test case
          if debug then tp { ctyp = (fst $ ctyp tp, coe)} else tp
   ]

  starts = ccats gr startcat

  hl f c1 c2 = f (c1 dummyHole) == f (c2 dummyHole)
--  applyHole = hl id -- TODO why doesn't this work for equality of contexts?
  applyHole = hl show -- :: (Tree -> Tree) -> (Tree -> Tree) -> Bool

  funs = case lookupSymbol gr funname of
           [] -> error $ "Function "++funname++" not found"
           fs -> fs

  cat_testcase_ctxs =
    [ (goalcat,(testcase,ctxs))
    | testcase <- treesUsingFun gr funs
    , let goalcat = ccatOf testcase -- never a coercion (coercions can't be goals)
    , let ctxs = [ ctx | st <- starts
                 , ctx <- contextsFor gr st goalcat ]
    ] :: [(ConcrCat, (Tree,[Tree->Tree]))]
  goalcats = map fst cat_testcase_ctxs

  coercion_goalcats_commonCtxs =
    [ (coe,coveredGoalcats,ctxs)
    | coe@(CC Nothing _) <- S.toList $ nonEmptyCats gr -- only coercions
    , let coveredGoalcats = filter (coerces gr coe) goalcats
    , let ctxs = [ ctx | st <- starts            -- Contexts that have
                 , ctx <- contextsFor gr st coe  -- a) hole of coercion, and are
                 , any (applyHole ctx) allCtxs ] -- b) relevant for the function we test
    , length coveredGoalcats >= 2 -- no use if the coercion covers 0 or 1 categories
    , not $ null ctxs ]

  allCtxs = [ ctx | (_,(_,ctxs)) <- cat_testcase_ctxs
                  , ctx <- ctxs ] :: [Tree->Tree]

  commonCtxs cat = nubBy applyHole [ ctx | (_,cats,ctxs) <- coercion_goalcats_commonCtxs
                                   , cat `elem` cats
                                   , ctx <- ctxs ] :: [Tree->Tree]


testTree :: Bool -> Grammar -> [Grammar] -> Tree -> Int -> [Tree -> Tree] -> Result
testTree debug gr tgrs t n ctxs = unlines
  [ "* " ++ {- show n ++ ")" ++ -} show t
  , showConcrFun gr w
  , if debug then unlines $ tabularPrint gr t else ""
  , unlines $ concat
       [ [ "** " ++ show m ++ ") " ++ show (ctx (App (hole c) []))
         , langName gr ++ linearize gr (ctx t)
         ] ++
         [ langName tgr ++ linearize tgr (ctx t)
         | tgr <- tgrs ]
       | (ctx,m) <- zip ctxs [1..]
       ]
 , "" ]
 where
  w = top t
  c = snd (ctyp w)
  langName gr = concrLang gr ++ "> "

  tabularPrint gr t =
    let cseqs = [ concatMap showCSeq cseq
                | cseq <- map (concrSeqs gr) (seqs $ top t) ]
        tablins = tabularLin gr t :: [(String,String)]
     in [ fieldname ++ ":\t" ++ lin ++ "\t" ++ s
        | ((fieldname,lin),s) <- zip tablins cseqs ]
  showCSeq (Left tok) = " " ++ show tok ++ " "
  showCSeq (Right (i,j)) = " <" ++ show i ++ "," ++ show j ++ "> "

--------------------------------------------------------------------------------
-- Generate test trees

treesUsingFun :: Grammar -> [Symbol] -> [Tree]
treesUsingFun gr detCNs =
  [ tree
    | detCN <- detCNs
    , let (dets_cns,np_209) = ctyp detCN -- :: ([ConcrCat],ConcrCat)
    , let bestArgs = case dets_cns of
                      [] -> [[]]
                      xs -> bestTrees detCN gr dets_cns
    , tree <- App detCN `map` bestArgs ]


bestTrees :: Symbol -> Grammar -> [ConcrCat] -> [[Tree]]
bestTrees fun gr cats =
  bestExamples fun gr $ take 200 -- change this to something else if too slow
  [ GF.featIthVec (feat gr) cats size i
  | all (`S.member` nonEmptyCats gr) cats
  , size <- [0..20]
  , let card = GF.featCardVec (feat gr) cats size
  , i <- [0..card-1]
  ]

subsumes :: (Eq a, Eq b) => [a] -> [b] -> Bool
xs `subsumes` ys = go (xs `zip` ys)
 where
  go [] =
    True

  go ((x,y):xys) =
    and [ y' == y | (x',y') <- xys, x == x' ] &&
    go [ xy | xy@(x',_) <- xys, x /= x' ]


bestExamples :: Symbol -> Grammar -> [[Tree]] -> [[Tree]]
bestExamples fun gr vtrees = map fst $ foldr f [] vtrees_lins
 where
  syncategorematics = concatMap (lefts . concrSeqs gr) (seqs fun)
  vtrees_lins = [ (vtree, syncategorematics ++
                  concatMap (map snd . tabularLin gr) vtree) --linearise all trees at once
                 | vtree <- vtrees ] :: [TestCase]

  -- This results in fewer example trees, but maybe misses some chances for bugs.
  -- vtrees_lins = [ (vtree,
  --                 (map snd . tabularLin gr) (App fun vtree)) --apply fun to trees and linearise result
  --                | vtree <- vtrees ] :: [([Tree],[String])]

  subsumesT :: TestCase -> TestCase -> Bool
  subsumesT (_,s) (_,t) = subsumes s t

  f :: TestCase -> [TestCase] -> [TestCase]
  f t ts = if any (`subsumesT` t) ts
             then ts
             else t : filter (not . subsumesT t) ts

type TestCase = ([Tree],[String])
