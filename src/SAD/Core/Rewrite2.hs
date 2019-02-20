{-# LANGUAGE FlexibleContexts #-}


module SAD.Core.Rewrite2 where

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

instance Eq Formula where  
  a == b = twins a b

can :: (t -> Maybe a) 
    -> t 
    -> Bool
can f = isJust . f


----Rewriting

--modified unification algorithm
--instantiating left-hand side of a formula to a term

--updating substitution function:
term_match :: Maybe (Formula -> Maybe Formula)
           -> [(Formula, Formula)] 
           -> Maybe (Formula -> Maybe Formula)
term_match env [] = env 
term_match env ((a,b):oth) =
  case (a,b) of 
    (Trm {trName = f, trArgs = fargs}, Trm {trName = g, trArgs = gargs})
      -> if f == g && length fargs == length gargs 
           then term_match env $ zip fargs gargs ++ oth
           else Nothing
    (Var {trName = varName} ,t) | (head varName == '?' || head varName == 'u')
      -> case env of 
           Just env'
             -> case env' a of 
                  Nothing -> term_match 
                    (Just (\c -> if c == a then Just t else env' c)) oth
                  Just b -> if b == t then term_match env oth
                                      else Nothing
           _ -> Nothing
    _ -> Nothing 


--term substitution
tsubst :: (Formula -> Maybe Formula) 
       -> Formula 
       -> Formula
tsubst sfn tm =
  case tm of 
    Var {trName = varName} | head varName == '?' || head varName == 'u'
      -> case sfn tm of
           Just sub -> sub
           _-> tm
    Trm {trName = f, trArgs = args, trId = n} 
      -> zTrm n f (map (tsubst sfn) args)
    _ -> error "tsubst: input is not a term"


--tries to find a rewrite rule in eqs that can be applied at the first position of some term t
rewrite1 :: [Formula] 
         -> Formula 
         -> Maybe Formula
rewrite1 eqs t =
  case eqs of
  (Trm "=" [l,r] _ equalityId):oeqs -> 
    let trmM = term_match (Just (\a -> Nothing)) [(l,t)]
    in case trmM of
         Just fn -> Just (tsubst fn r)
         _ -> rewrite1 oeqs t
  _ -> Nothing 


--rewriting of arbitrary terms  
rewriter :: [Formula] 
         -> Formula 
         -> Formula
rewriter eqs tm = 
  let r = rewrite1 eqs tm
  in if isJust r 
       then rewriter eqs (fromJust r)
       else case tm of 
              Var {} -> tm
              Trm {trName = f, trArgs = args, trId = n} 
                -> let newArgs = map (rewriter eqs) args
                       tm' = zTrm n f newArgs
                   in if tm' == tm then tm else rewriter eqs tm' 

