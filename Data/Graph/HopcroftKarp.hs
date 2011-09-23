{-# LANGUAGE ScopedTypeVariables, TransformListComp, ViewPatterns #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Graph.HopcroftKarp
-- Copyright   :  (c) 2011 Hexagram 49, Inc. (see LICENSE)
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ivan.Tarasov@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Library for finding a maximum cardinality matching in a bipartite graph using Hopcroft-Karp algorithm.
--
-----------------------------------------------------------------------------

module Data.Graph.HopcroftKarp (
  -- * Matching functions
  findMatching,
  findMatching',
  -- * Datatypes
  L(..),
  R(..),
  LR,
  -- * Convenience functions
  (-->),
  (--->),
  numberVertices
) where

import Control.Applicative
import Control.Monad (forM_, unless, when)
import Control.Monad.ST.Strict
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Cont
import Data.Array
import Data.STRef
import qualified Data.IntSet as IS; import Data.IntSet (IntSet)
import qualified Data.IntMap as IM; import Data.IntMap (IntMap)
import qualified Data.Map as M; import Data.Map (Map)
import Data.List (find, foldl')
import GHC.Exts (sortWith)
import Data.Tuple (swap)

-- | Convenience function to simplify entry of adjacent nodes.
(-->) :: a -> b -> (a, b)
l --> r = (l, r)

-- | Convenience function to simplify entry of adjacent nodes.
(--->) :: Int -> Int -> LR
l ---> r = L l --> R r

-- | Newtype alias for a node in the left vertex subset of the bipartite graph.
newtype L = L { unL :: Int } deriving (Eq, Ord, Ix)
-- | Newtype alias for a node in the right vertex subset of the bipartite graph.
newtype R = R { unR :: Int } deriving (Eq, Ord, Ix)

instance Show L where show (L l) = show l
instance Show R where show (R r) = show r

type LR = (L, R)

data LPred = Matched | FirstLayer | LPred R deriving (Show,Eq)

-- | Finds a maximum cardinality bipartite matching for a bipartite graph.
findMatching :: forall l r. (Ord l, Ord r)
             => [(l, r)]      -- ^ Edges between L and R.
             -> [(l, r)]      -- ^ Maximum cardinality matching (from L to R).
findMatching es = map convertLR $ findMatching' edges n m
  where
    -- | We assign the numbers to unique vertices on the left and on the right,
    -- and store them in arrays, where the array index is the number of the vertex.
    edges :: [LR]
    numberedLs :: Array Int l
    numberedRs :: Array Int r
    n, m :: Int
    (edges, numberedLs, numberedRs) = numberVertices es
    n = rangeSize (bounds numberedLs)
    m = rangeSize (bounds numberedRs)

    convertLR :: LR -> (l, r)
    convertLR (L l, R r) = (numberedLs ! l, numberedRs ! r)

-- | Finds a maximum cardinality bipartite matching for a bipartite graph.
-- Assumes that the edges are numbered from @0@ to @n-1@ and @0@ to @m-1@ in the
-- left and right vertex subsets of the bipartite graph.
--
-- This function doesn't do any renumbering and may be inefficient if the
-- integer indices of the vertices are sparse. For a more general function, see
-- 'findMatching', which does vertex (re)numbering.
findMatching' :: [LR] -- ^ Edges between L and R.
              -> Int  -- ^ Size of L.
              -> Int  -- ^ Size of R.
              -> [LR]
findMatching' edges n m = loop initialMatching
  where
    -- | A map from vertices in L to a list of vertices in R
    adjacent :: Array L [R]
    adjacent = accumArray (flip (:)) [] (L 0,L $ n-1) edges

    -- | Start with a greedy matching. That's redundant but more efficient.
    -- Matching is from a vertex in R to a vertex in L
    initialMatching :: IntMap L
    initialMatching = foldl' (\matching (unL -> l,map unR -> rs) -> 
                        case find (not . (`IM.member` matching)) rs of
                          Nothing -> matching
                          Just r  -> IM.insert r (L l) matching
                      ) IM.empty $ assocs adjacent

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
                                      , r <- adjacent ! l
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

-- | Take a list of pairs of vertices from left and right vertex sets and number them starting from @0@ (left and right sets are numbered separately).
--
-- Returns a triple, consisting of list of 'LR' edges, and two arrays from integers to the left and right vertices respectively.
numberVertices :: (Ord l, Ord r)
               => [(l, r)]
               -> ([LR], Array Int l, Array Int r)
numberVertices es =
    let (lsMap, rsMap, edges) = foldl' addEdge (M.empty, M.empty, []) es
        n = M.size lsMap
        m = M.size rsMap
      in
        ( edges
        , array (0,n-1) (map swap $ M.toList lsMap)
        , array (0,m-1) (map swap $ M.toList rsMap)
        )
        
  where
    addEdge :: (Ord l, Ord r) => (Map l Int, Map r Int, [LR]) -> (l, r) -> (Map l Int, Map r Int, [LR])
    addEdge (lsMap, rsMap, edges) (l,r) = (lsMap', rsMap', (L lIdx --> R rIdx) : edges)
      where
        (lIdx, lsMap') = l `insertOrReturnIdx` lsMap
        (rIdx, rsMap') = r `insertOrReturnIdx` rsMap

    insertOrReturnIdx :: Ord x => x -> Map x Int -> (Int, Map x Int)
    insertOrReturnIdx x idxMap = case x `M.lookup` idxMap of
        Nothing  -> let idx = M.size idxMap in idx `seq` (idx, M.insert x idx idxMap)
        Just idx -> (idx, idxMap)

