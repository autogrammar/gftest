{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module GrammarBuild
  ( readGrammar
  , toGrammar
  ) where

import Data.Char
import Data.List
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S
import Debug.Trace
import GrammarTypes
import qualified GrammarFeat as GF
import qualified GrammarCoercion as GCo
import qualified GrammarContexts as GCtx
import Grammar
  ( Grammar(..)
  , mkTree
  , ctxEnv
  , arity
  , uncoerceAbsCat
  )
import GHC.Exts (the)
import qualified Mu
import qualified PGF2
import qualified PGF2.Internal as I

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

        , lookupSymbol = GCo.lookupAll (symb2table `map` symbols gr)

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
