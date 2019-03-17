{-
Author: Annika Hennes (2019)

Testing whether a term rewriting system is confluent
-}
{-# LANGUAGE FlexibleContexts #-}


module SAD.Core.Confluence where

import SAD.Core.SourcePos
import SAD.Data.Formula
import SAD.Data.Rules (Rule)
import qualified SAD.Data.Rules as Rule
import SAD.Data.Text.Context (Context)
import qualified SAD.Data.Text.Context as Context
import qualified SAD.Data.Text.Block as Block (body, link, position)
import SAD.Core.Base
import qualified SAD.Core.Message as Message
import SAD.Core.Thesis
import SAD.Core.Reason
import SAD.Core.Rewrite
import SAD.Prove.Unify
import SAD.Core.Rewrite2
import SAD.Core.CriticalPairs

import Data.List
import Data.Maybe
import qualified Data.IntMap.Strict as IM
import qualified Data.Set as Set
import Control.Monad.State
import Data.Either
import Control.Monad.Reader
import Control.Monad

import Debug.Trace
import Data.Typeable


{-tests whether the critical pairs in a term rewriting system are joinable-}
confluence_crit_pairs :: [Formula] 
                      -> [Formula]  
                      -> Bool
confluence_crit_pairs cp trs =
  case cp of
    [] -> True
    (Trm {trName = "=",trArgs = [l,r]}):rest 
      -> rewriter trs l == rewriter trs r && confluence_crit_pairs rest trs 
    _ -> error "confluence_crit_pairs: non-equational argument in list"


{-tests whether a terminating term rewriting system is confluent-}
confluence :: [Formula] 
           -> Bool
confluence trs =
  let cp = all_critical_pairs trs
  in confluence_crit_pairs cp trs
