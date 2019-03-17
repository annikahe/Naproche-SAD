{-
Author: Annika Hennes (2019)

Computing the critical pairs of a term rewriting system
-}
{-# LANGUAGE FlexibleContexts #-}


module SAD.Core.CriticalPairs where

import SAD.Core.SourcePos
import SAD.Data.Formula
import SAD.Data.Rules (Rule)
import qualified SAD.Data.Rules as Rule
import SAD.Data.Text.Context (Context)
import qualified SAD.Data.Text.Context as Context
import qualified SAD.Data.Text.Block as Block (body, link, position)
import qualified SAD.Data.Text.Decl as Decl
import SAD.Core.Base
import qualified SAD.Core.Message as Message
import SAD.Core.Thesis
import SAD.Core.Reason
import SAD.Core.Rewrite
import SAD.Prove.Unify
import SAD.Core.Rewrite2

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
                   

{-rename variables occurring in two terms such that they have no variables in common-}
renamepair :: Formula 
           -> Formula 
           -> (Formula, Formula)
renamepair tm1 tm2 =
  let fvs1 = fv tm1
      fvs2 = fv tm2
      (nms1,nms2) = splitAt (length fvs1) 
        $ map (\n -> zVar ("?a" ++ show n)) 
          [0..(length fvs1 + length fvs2 - 1)] 
  in (substs tm1 (map trName fvs1) nms1, 
      substs tm2 (map trName fvs2) nms2)


--computing all critical pairs

{-updating the substitution formula recursively-}
listcases :: (Formula -> (m (Formula -> Formula) -> Formula -> Maybe Formula) -> [Formula]) 
          -> (m (Formula -> Formula) -> [Formula] -> Maybe Formula) 
          -> [Formula] 
          -> [Formula] 
          -> [Formula]
listcases fn rfn lis acc = 
  case lis of
    [] -> acc
    h:t -> fn h (\i h' -> rfn i $ h':t) ++ 
            listcases fn (\i t' -> rfn i $ h:t') t acc


{-finds all critical overlaps between a left-hand side of a rule and another term-}
overlaps :: MonadPlus m 
         => (Formula, Formula) 
         -> Formula 
         -> (m (Formula -> Formula) -> Formula -> Maybe Formula) 
         -> [Formula]
overlaps (l,r) tm rfn =
    case tm of
      Trm name args _ n 
        -> listcases (overlaps (l,r)) (\i a -> rfn i $ zTrm n name a) 
              args (maybeToList $ rfn (unif [(l,tm)]) r) 
      Var {} -> []


crit1 :: Formula 
      -> Formula 
      -> [Formula]
crit1 Trm{trName ="=",trArgs = [l1,r1]} Trm{trName ="=",trArgs = [l2,r2]} = 
  overlaps (l1,r1) l2 (\ unifct t ->  unifct <*> pure (zEqu t r2))
crit1 _ _ = error "crit1: non-equational argument"


{-computes all critical pairs of two formulas-}
critical_pairs :: Formula 
               -> Formula 
               -> [Formula]
critical_pairs fma fmb =
  let (fm1,fm2) = renamepair fma fmb in
  if twins fma fmb then crit1 fm1 fm2
                   else union (crit1 fm1 fm2) (crit1 fm2 fm1)


{-computes all critical pairs of a term rewriting system-}
all_critical_pairs :: [Formula] -> [Formula]
all_critical_pairs trs = 
  nub $ concat $ [critical_pairs a b | (a:rest) <- tails trs, b <- (a:rest)]
