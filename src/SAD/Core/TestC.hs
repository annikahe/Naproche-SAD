{-
Author: Annika Hennes (2019)

Testing of the Knuth-Bendix Completion and related functions
-}
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


-- create functions for testing     

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

makeConsta :: Formula
makeConsta = zTrm (-22) "a" []

makeConstb :: Formula
makeConstb = zTrm (-23) "b" []

makeConstTrue :: Formula 
makeConstTrue = zTrm (-24) "true" []

makeFunOr :: [Formula] -> Formula
makeFunOr args = zTrm (-25) "or" args

makeNeg :: Formula -> Formula
makeNeg arg = zTrm (-26) "-" [arg]


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
      tm1 = makeMul [makeInv a,makeMul [makeInv (makeInv a),b]] -- inv(a)*(inv(inv(a))*b)
      tm2 = makeMul [a,makeMul [makeInv a,b]] --a*(inv(a)*b)
  in wordProb wts trs tm1 tm2


testGrp = -- on my computer, this takes a few minutes. Please be patient.
  let x = zVar "?x"
      y = zVar "?y"
      z = zVar "?z"
      e = makeNeutr
      a = makeConsta
      b = makeConstb
      ass = zEqu (makeMul [makeMul [x,y],z]) (makeMul [x,makeMul [y,z]]) --(x*y)*z = x*(y*z)
      neutr = zEqu (makeMul [x,e]) x --x*1=x
      inv = zEqu (makeMul [x,makeInv x]) e --x*i(x)=1
      wts = ["e","*","inv"]
      eqs = [neutr,inv,ass]
  in complete_and_simplify wts eqs 

test2 = --Ex. 6.4
  let x = zVar "?x"
      fgf = makeFunf [makeFung [makeFunf [x]]] --f(g(f(x)))
      g = makeFung [x] --g(x)
      eq = zEqu fgf g --f(g(f(x))) = g(x)
  in confluence [eq] -- => not confluent 

test2complete = 
  let x = zVar "?x"
      fgf = makeFunf [makeFung [makeFunf [x]]] --f(g(f(x)))
      g = makeFung [x] --g(x)
      eq = zEqu fgf g --f(g(f(x))) = g(x)
      wts = ["f","g"]
  in complete_and_simplify wts [eq] -- [g(g(f(?a0))) = f(g(g(?a0))),f(g(f(?x))) = g(?x)]

test3 = --Ex. 6.6
  let x = zVar "?x"
      f = makeFunf [x]
      ff = makeFunf [f]
      g = makeFung [x]
      gg = makeFung [g]
      fg = makeFunf [g]
      gf = makeFung [f]
      eq1 = zEqu ff f --f(f(x)) = f(x)
      eq2 = zEqu gg f --g(g(x)) = f(x)
      eq3 = zEqu fg g --f(g(x)) = g(x)
      eq4 = zEqu gf g --g(f(x)) = g(x)
  in confluence [eq1,eq2,eq3,eq4] -- => confluent

test3complete = 
  let x = zVar "?x"
      f = makeFunf [x]
      ff = makeFunf [f]
      g = makeFung [x]
      gg = makeFung [g]
      fg = makeFunf [g]
      gf = makeFung [f]
      eq1 = zEqu ff f --f(f(x)) = f(x)
      eq2 = zEqu gg f --g(g(x)) = f(x)
      eq3 = zEqu fg g --f(g(x)) = g(x)
      eq4 = zEqu gf g --g(f(x)) = g(x)
      wts = ["f","g"]
  in complete_and_simplify wts [eq1,eq2,eq3,eq4] -- => outputs [f(f(?x)) = f(?x),g(g(?x)) = f(?x),f(g(?x)) = g(?x),g(f(?x)) = g(?x)] = [eq1,eq2,eq3,eq4]

test4 = --Ex. 6.5 (c)
  let x = zVar "?x"
      a = makeConsta 
      b = makeConstb
      eq1 = zEqu (makeFunf [x,x]) a
      eq2 = zEqu (makeFunf [x,makeFung [x]]) b
  in confluence [eq1,eq2] -- => confluent

test5 = --Ex.6.10
  let x = zVar "?x"
      y = zVar "?y"
      eq = zEqu (makeFunf [x]) (makeFung [x,y])
  in putStr ("Critical Pairs: "++ show (all_critical_pairs [eq])++"\n"++"Confluent? "++show (confluence [eq])++"\n")
  -- => not confluent (more variables in the right-hand side than in the left-hand side)

test6 = --Ex. 7.2
  let x = zVar "?x"
      y = zVar "?y"
      z = zVar "?z"
      eq1 = zEqu (makeMul [makeMul [x,y],makeMul [y,z]]) y --(x*y)*(y*z) = y
      eq2 = zEqu (makeMul [x,makeMul[makeMul [x,y],z]]) (makeMul [x,y]) -- x*((x*y)*z) = x*y
      eq3 = zEqu (makeMul [makeMul [x,makeMul [y,z]],z]) (makeMul [y,z]) -- (x*(y*z))*z = y*z
  in confluence [eq1,eq2,eq3] -- => confluent

test7 =
  let x = zVar "?x"
      trs = [zEqu (makeFunf [makeFunf [x]]) (makeFung [x])] -- f(f(x)) = g(x)
      wts = ["g","f"]
  in complete_and_simplify wts trs -- => [f(g(?a0)) = g(f(?a0)),f(f(?x)) = g(?x)] 

testCritPairs =
  let a = zVar "?a"
      b = zVar "?b"
      inva = makeInv a --Inv(a)
      mulab = makeMul [a,b] -- a*b
      mulinvmul = makeMul [inva,mulab] --Inv(a)*(a*b)
      eq = [zEqu mulinvmul b] -- Inv(a)*(a*b) = b
      wts = ["e","*","inv"]
      c1 = head (all_critical_pairs eq)
      eq' = case c1 of
             Trm{trId = equalityId,trArgs = [l,r]} 
               -> [zEqu (rewriter eq r) (rewriter eq l)]
  in all_critical_pairs (eq'++eq)

  
testCritPairs2 =
  let x = zVar "?x"
      fgf = makeFunf [makeFung [makeFunf [x]]] --f(g(f(x)))
      g = makeFung [x] --g(x)
      eq = zEqu fgf g --f(g(f(x))) = g(x)
      trs = [eq] 
      wts = ["f","g"]
      c1 = head (all_critical_pairs trs)
      trs' = case c1 of
              Trm{trId = equalityId,trArgs = [l,r]} 
                -> [zEqu (rewriter trs l) (rewriter trs r)]
  in putStr (show (all_critical_pairs trs) ++ "\n" ++ show (all_critical_pairs (trs'++trs)) ++ "\n")
