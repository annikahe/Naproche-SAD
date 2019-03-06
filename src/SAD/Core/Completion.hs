{-# LANGUAGE FlexibleContexts #-}


module SAD.Core.Completion where

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


----completion

--adding rules respecting the ordering
normalize_and_orient :: (Formula -> Formula -> Bool) 
                     -> [Formula]
                     -> Formula
                     -> Maybe (Formula, Formula)
normalize_and_orient ord rules Trm{trName = "=",trArgs = [s,t]} = 
  let nfs = rewriter rules s 
      nft = rewriter rules t
  in if (ord nfs nft) then return (nfs,nft) 
                      else if (ord nft nfs) then return (nft,nfs) 
                                            else Nothing
normalize_and_orient ord rules _ = 
  error "normalize_and_orient: non-equational input"                          


--help function for updating the three lists in complete
updateTrip :: Maybe (Formula,Formula) 
           -> ([Formula],[Formula],[Formula]) 
           -> ([Formula],[Formula],[Formula])
updateTrip (Just (s,t)) (eqs,def,eq:ocrits)
  | twins s t = (eqs,def,ocrits)
  | otherwise = 
      let eq' = zEqu s t
          eqs' = eq':eqs 
      in (eqs',def,ocrits ++ foldr ((++) . (critical_pairs  eq')) [] eqs')
updateTrip _ (eqs,def,eq:ocrits) = (eqs,eq:def,ocrits)
updateTrip _ _ = error "updateTrip: no critical pairs"


--basic completion of a term rewriting system
complete :: (Formula -> Formula -> Bool)
         -> ([Formula], [Formula], [Formula]) 
         -> [Formula]
complete ord (eqs,def,eq:ocrits) =
  let st = normalize_and_orient ord eqs eq
      trip = updateTrip st (eqs,def,eq:ocrits)
  in complete ord trip
complete ord (eqs,def,_) 
  | def == [] = eqs 
  | otherwise =
      let e = maybeToList (find (can (normalize_and_orient ord eqs)) def)
      in if e == [] then error "complete: non-orientable equation" --prevent infinite loop
                    else complete ord (eqs, (nub def) \\ e,e)    


--removing redundant rules from a completed term rewriting system
interreduce :: [Formula] 
            -> [Formula] 
            -> [Formula]
interreduce dun eqs =
  case eqs of
    (Trm {trName = "=",trArgs = [l,r]}):oeqs ->
      let dun' = if twins (rewriter (dun ++ oeqs) l) l 
                   then (zEqu l (rewriter (dun ++ eqs) r)):dun
                   else dun 
      in interreduce dun' oeqs
    [] -> reverse dun
    _ -> error "interreduce: non-equational argument"


help_normalize :: (Formula -> Formula -> Bool) 
               -> Formula 
               -> Maybe Formula
help_normalize ord fml = 
  let tuple = normalize_and_orient ord [] fml
  in tuple >>= (\ (s,t) -> Just (zEqu s t))


--gets a list of strings as weights (descending weights) and completes and interreduces a term rewriting system
--this is the most important function
complete_and_simplify :: [String] 
                      -> [Formula] 
                      -> [Formula]
complete_and_simplify wts eqs =
  let ord = lpo_ge (weight wts)
      maybeList = map (help_normalize ord) eqs
      eqs' = catMaybes maybeList
  in ((interreduce []) . (complete ord)) (eqs',[], all_critical_pairs eqs')


only_complete :: [String] 
              -> [Formula] 
              -> [Formula]
only_complete wts eqs =
  let ord = lpo_ge (weight wts)
      maybeList = map (help_normalize ord) eqs
      eqs' = catMaybes maybeList
  in trace ("crits: "++show (all_critical_pairs eqs')) (complete ord) (eqs',[], all_critical_pairs eqs')