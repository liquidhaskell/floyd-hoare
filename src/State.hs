{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module State where

import Prelude hiding ((++), const, max)
import Language.Haskell.Liquid.ProofCombinators

type GState = Map

{-@ reflect def @-}
def :: v -> Map k v
def v = Def v

data Map k v = Def v | Set k v (Map k v)

{-@ reflect set @-}
set :: k -> v -> Map k v -> Map k v
set k v s = Set k v s

{-@ reflect get @-}
get :: (Eq k) => Map k v -> k -> v
get (Def v)     _   = v
get (Set k v s) key = if key == k then v else get s key

{-@ lemma_get_set :: k:_ -> v:_ -> s:_ -> { get (set k v s) k == v }  @-}
lemma_get_set :: k -> v -> Map k v -> Proof 
lemma_get_set _ _ _ = () 

{-@ lemma_get_not_set :: k':_ -> k:{k /= k'} -> val:_ -> s:_ 
                      -> { get (set k val s) k' = get s k' }  
  @-}
lemma_get_not_set :: k -> k -> v -> Map k v -> Proof 
lemma_get_not_set _ _ _ (Def {}) = ()
lemma_get_not_set _ _ _ (Set {}) = ()
