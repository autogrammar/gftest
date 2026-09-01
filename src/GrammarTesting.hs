{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module GrammarTesting
  ( diffCats
  , hasConcrString
  , Comparison(..)
  , dummyHole
  , compareTree
  , testFun
  , testTree
  , treesUsingFun
  ) where

import Data.Either (lefts)
import Data.List
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S
import Debug.Trace
import GrammarTypes
import qualified GrammarFeat as GF
import Grammar
  ( Grammar(..)
  , contextsFor
  , ccats
  , coerces
  , coercions
  , concrCats
  , concrLang
  , concrSeqs
  , feat
  , linearize
  , lookupSymbol
  , nonEmptyCats
  , showConcrFun
  , symbols
  , tabularLin
  )

type Result = String

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
