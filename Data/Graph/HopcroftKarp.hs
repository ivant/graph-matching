{-# LANGUAGE ScopedTypeVariables, TransformListComp, ViewPatterns #-}
module Data.Graph.HopcroftKarp (
  L(..), R(..),
  LR,
  (-->),
  findMatching
) where

import Control.Applicative
import Control.Monad (forM_, unless, when)
import Control.Monad.ST.Strict
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Cont
import Data.Array
import Data.STRef
import qualified Data.IntMap as IM; import Data.IntMap (IntMap)
import Data.List (find, foldl')
import GHC.Exts (sortWith)

newtype L = L { unL :: Int } deriving (Eq, Ord, Ix)
newtype R = R { unR :: Int } deriving (Eq, Ord, Ix)

instance Show L where show (L l) = show l
instance Show R where show (R r) = show r

type LR = (L, R)

(-->) :: Int -> Int -> LR
a --> b = (L a, R b)

data LPred = Matched | FirstLayer | LPred R deriving (Show,Eq)

-- | Finds a maximal cardinality bipartite matching for a bipartite graph.
findMatching :: Int   -- ^ number of vertices in L
             -> Int   -- ^ number of vertices in R
             -> [LR]  -- ^ edges between L and R. In each set vertices are numbered from 0.
             -> [LR]  -- ^ maximum cardinality matching (from L to R)
findMatching n m es = loop initialMatching
  where
    -- | A map from vertices in L to a list of vertices in R
    adj :: IntMap [R]
    adj = IM.fromList [ (head l, r) | (L l, r) <- es, then group by l ]

    -- | Start with a greedy matching. That's redundant but more efficient.
    -- Matching is from a vertex in R to a vertex in L
    initialMatching :: IntMap L
    initialMatching = foldl' (\m (l,map unR -> rs) -> 
                        case find (not . (`IM.member` m)) rs of
                          Nothing -> m
                          Just r  -> IM.insert r (L l) m
                      ) IM.empty $ IM.toList adj
    convertMatching :: IntMap L -> [LR]
    convertMatching m = [ (l, R r) | (r,l) <- IM.toList m ]

    loop :: IntMap L  -- ^ current matching (map from R to L)
         -> [LR]
    loop matching =
        let rPreds = accumArray undefined [] (R 0,R $ m-1) []
            lPred = accumArray (\_ _ -> Matched) FirstLayer (L 0, L $ n-1) [ (l,()) | l <- IM.elems matching ]
            layer = map fst . filter ((==FirstLayer) . snd) $ assocs lPred -- layer :: [L]
            (rPreds', lPred', unmatched) = bfs layer rPreds lPred
          in
            if null unmatched then
                convertMatching matching
              else loop $ runST $ do
                matchingRef <- newSTRef matching
                rPredsRef <- newSTRef rPreds'
                lPredRef <- newSTRef lPred'

                -- recursively search backwards through layers to find adjusting paths
                forM_ unmatched (dfs matchingRef rPredsRef lPredRef)

                readSTRef matchingRef
      where
        dfs :: forall s.
               STRef s (IntMap L)           -- ^ current matching
            -> STRef s (Array R [L])        -- ^ R predecessors
            -> STRef s (Array L LPred)      -- ^ L predecessors
            -> R                            -- ^ search from this vertex
            -> ST s Bool
        dfs matchingRef rPredsRef lPredRef r = recurse r
          where
            recurse :: R -> ST s Bool
            recurse r = (`runContT` return) $ callCC $ \cont -> do
                rPreds <- lift $ readSTRef rPredsRef
                let ls = rPreds ! r
                unless (null ls) $ do
                  -- remove r from rPreds
                  lift $ writeSTRef rPredsRef (rPreds // [(r, [])])

                  forM_ ls $ \l -> do
                    lPred <- lift $ readSTRef lPredRef
                    let lp = lPred ! l
                    unless (lp == Matched) $ do
                      -- remove l from lPred
                      lift $ writeSTRef lPredRef (lPred // [(l, Matched)])

                      let adjustPath = do
                            lift $ modifySTRef matchingRef (IM.insert (unR r) l)
                            cont True
                      case lp of
                        FirstLayer -> adjustPath
                        LPred r'   -> do
                            leadsToFirstLayer <- lift $ recurse r'
                            when leadsToFirstLayer adjustPath
                return False

        bfs :: [L]                        -- ^ BFS roots
            -> Array R [L]                -- ^ array of predecessors for vertices in R
            -> Array L LPred              -- ^ array of predecessors for vertices in L
            -> (Array R [L],              --   final array of R predecessors
                Array L LPred,            --   final array of L predecessors
                [R])                      --   list of unmatched vertices in R
        bfs layer rPreds lPred = 
            let rLayer :: [(R, [L])]
                rLayer = [ (head r,l) | l <- layer
                                      , r <- adj IM.! unL l
                                      , null (rPreds ! r)
                                      , then group by r
                                      ]
                rPreds' = rPreds // rLayer
                (layer', lPredUpdate, unmatched) = foldl' (\(ls,lps,us) (r,ps) ->
                    case unR r `IM.lookup` matching of
                      Just l  -> (l:ls, (l,LPred r):lps, us)
                      Nothing -> (ls, lps, r:us)
                  ) ([], [], []) rLayer
                lPred' = lPred // lPredUpdate
              in
                if not (null layer') && null unmatched then
                    bfs layer' rPreds' lPred'
                  else
                    (rPreds', lPred', unmatched)

