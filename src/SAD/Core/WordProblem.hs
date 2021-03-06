{-
Author: Annika Hennes (2019)

solving the word problem for finite and terminating rewrite systems
-}
{-# LANGUAGE FlexibleContexts #-}


module SAD.Core.WordProblem where

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
import SAD.Core.Confluence
import SAD.Core.Completion

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


{-input: weighting, term rewriting system and two terms
  output: boolean value that determines whether the two terms are equal-}
wordProb :: [String] 
         -> [Formula] 
         -> Formula 
         -> Formula 
         -> Bool
wordProb wts trs tm1 tm2 =
  let trs' = if confluence trs == False 
                then complete_and_simplify wts trs
                else trs
      tm1' = rewriter trs' tm1
      tm2' = rewriter trs' tm2
  in tm1' == tm2'

