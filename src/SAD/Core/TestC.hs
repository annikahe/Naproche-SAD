{-# LANGUAGE FlexibleContexts #-}


module SAD.Core.TestC where

import SAD.Core.SourcePos
import SAD.Data.Formula
import SAD.Data.Rules (Rule)
import qualified SAD.Data.Rules as Rule
import SAD.Data.Text.Context (Context)
import qualified SAD.Data.Text.Context as Context
import qualified SAD.Data.Text.Block as Block (body, link, position)
import SAD.Core.Base
import qualified SAD.Core.Message as Message
-- import SAD.Data.Instr
import SAD.Core.Thesis
import SAD.Core.Reason
import SAD.Core.Rewrite
import SAD.Prove.Unify
import SAD.Core.Rewrite2
import SAD.Core.Confluence
import SAD.Core.CriticalPairs
import SAD.Core.Completion
import SAD.Core.WordProblem

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


-- create certain functions for testing     

makeFunf :: [Formula] -> Formula
makeFunf args = zTrm (-15) "f" args

makeFung :: [Formula] -> Formula
makeFung args = zTrm (-16) "g" args

makeAdd :: [Formula] -> Formula
makeAdd args = zTrm (-17) "+" args 

makeSucc :: Formula -> Formula
makeSucc arg = zTrm (-18) "succ" [arg]

makeMul :: [Formula] -> Formula
makeMul args = zTrm (-19) "*" args

makeInv :: Formula -> Formula
makeInv arg = zTrm (-20) "inv" [arg]

makeNeutr :: Formula
makeNeutr = zTrm (-21) "e" []


---Testing

testComplete =
  let a = zVar "?a"
      b = zVar "?b"
      inva = makeInv a --Inv(a)
      mulab = makeMul [a,b] -- a*b
      mulinvmul = makeMul [inva,mulab] --Inv(a)*(a*b)
      eq = [zEqu mulinvmul b] -- Inv(a)*(a*b) = b
      wts = ["e","*","inv"]
  in complete_and_simplify wts eq -- => Confluent


testConfluence =
  let a = zVar "?a"
      b = zVar "?b"
      inva = makeInv a -- Inv(a)
      mulab = makeMul [a,b] -- a*b
      mulinvmul = makeMul [inva,mulab] --Inv(a)*(a*b)
      eq = [zEqu mulinvmul b] -- Inv(a)*(a*b) = b
      wts = ["e","*","inv"]
  in confluence eq -- => not confluent

testWP = 
  let a = zVar "?a"
      b = zVar "?b"
      inva = makeInv a -- Inv(a)
      mulab = makeMul [a,b] -- a*b
      mulinvmul = makeMul [inva,mulab] --Inv(a)*(a*b)
      trs = [zEqu mulinvmul b] -- Inv(a)*(a*b) = b
      wts = ["e","*","inv"] 
      tm1 = makeMul [makeInv a,makeMul [makeInv (makeInv a),b]]
      tm2 = makeMul [a,makeMul [makeInv a,b]]
  in wordProb wts trs tm1 tm2
