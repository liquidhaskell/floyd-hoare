--------------------------------------------------------------------------------
-- | Meta-theory for Axiomatic semantics 
--------------------------------------------------------------------------------

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

{-# LANGUAGE GADTs #-}

module Proof.FH where

import           Prelude hiding ((++)) 
import           Language.Haskell.Liquid.ProofCombinators
import qualified State as S
import           Programs
import           FloydHoare 

--------------------------------------------------------------------------------
-- | Problem 1: Legit 
--------------------------------------------------------------------------------

{- Recall the definition of `Legit` given in Axiomatic.hs 
  
   type Legit P C Q =  s:{State | bval P s} 
                    -> s':_ -> Prop (BStep C s s') 
                    -> {bval Q s'} 

 -}

--------------------------------------------------------------------------------
-- | The following lemmas prove our rules for `Consequence` are `Legit`
--------------------------------------------------------------------------------
{-@ lem_conseq_pre :: p':_ -> p:_ -> q:_ -> c:_ 
                   -> Imply p' p -> Legit p c q 
                   -> Legit p' c q
  @-}
lem_conseq_pre :: Assertion -> Assertion -> Assertion -> Com -> Valid -> Legit -> Legit 
lem_conseq_pre p' p q c impl pcq = \s s' c_s_s' -> 
  pcq (s ? (impl s)) s' c_s_s'

{-@ lem_conseq_post :: p:_ -> q:_ -> q':_ -> c:_ 
                    -> Legit p c q -> Imply q q' 
                    -> Legit p c q'
  @-}
lem_conseq_post :: Assertion -> Assertion -> Assertion -> Com -> Legit -> Valid -> Legit 
lem_conseq_post p q q' c pcq impl = \s s' c_s_s' -> 
  pcq s s' c_s_s' ? (impl s') 

--------------------------------------------------------------------------------
-- | The following lemma proves that our rule for `Skip` is `Legit` 
--------------------------------------------------------------------------------
{-@ lem_skip :: p:_ -> (Legit p Skip p) @-}
lem_skip :: Assertion -> Legit 
lem_skip p = \s s' (BSkip {}) -> () 

--------------------------------------------------------------------------------
-- | The following lemma proves that our rule for `Assign` is `Legit` 
--------------------------------------------------------------------------------
{-@ lem_asgn :: x:_ -> a:_ -> q:_ -> 
      Legit (bsub x a q) (Assign x a) q 
  @-}
lem_asgn :: Id -> AExp -> Assertion -> Legit 
lem_asgn x a q = \s s' (BAsgn {}) -> lemBsub x a q s

--------------------------------------------------------------------------------
-- | PROBLEM 1.a : Complete the proof that the rule for `Seq` is `Legit`
--------------------------------------------------------------------------------
{-@ lem_seq :: c1:_ -> c2:_ -> p:_ -> q:_ -> r:_ 
            -> Legit p c1 q 
            -> Legit q c2 r 
            -> Legit p (Seq c1 c2) r 
  @-}
lem_seq :: Com -> Com -> Assertion -> Assertion -> Assertion -> Legit -> Legit -> Legit 
lem_seq c1 c2 p q r l1 l2 = \s s' (BSeq _ _ _ smid _ t1 t2) -> 
  l1 s smid t1 &&& l2 smid s' t2

-- l1 :: Legit p c1 q , l2 :: Legit p c2 q
-- t1 :: Prop(BSeq c1 s smid), t2 :: Prop(BSeq c2 smid s')
-- thus, l1 s smid t1 :: { bval q smid }
--       l2 smid s' t2 :: { bval r s' }, given the above
-- so it suffices to cite both of these proofs to convince the SMT solver

-- HINT: Your goal is to prove that `bval r s'` -- i.e. s' "satisfies" the postcondition `r` 
--       What are the types of `l1` and `l2`, and `t1` and `t2`? How can you use them 
--       to prove your goal?


--------------------------------------------------------------------------------
-- | PROBLEM 1.b: Complete the proof that the rule for `If` is `Legit` 
--------------------------------------------------------------------------------
{-@ lem_if :: b:_ -> c1:_ -> c2:_ -> p:_ -> q:_ 
           -> Legit (bAnd p b)       c1 q 
           -> Legit (bAnd p (Not b)) c2 q 
           -> Legit p (If b c1 c2)  q
  @-}
lem_if :: BExp -> Com -> Com -> Assertion -> Assertion -> Legit -> Legit -> Legit
lem_if b c1 c2 p q l1 l2 = \s s' bs -> 
  case bs of 
    BIfT _ _ _ _ _ c1_s_s' -> 
      l1 s s' c1_s_s' 
    BIfF _ _ _ _ _ c2_s_s' -> 
      l2 s s' c2_s_s' 
   
--------------------------------------------------------------------------------
-- | PROBLEM 1.c: Complete the proof that the rule for `While` is `Legit`
--------------------------------------------------------------------------------
{-@ lem_while :: b:_ -> c:_ -> inv:_ 
              -> Legit (bAnd inv b) c inv
              -> Legit inv (While inv b c) (bAnd inv (Not b)) 
  @-}
lem_while :: BExp -> Com -> Assertion -> Legit -> Legit 
lem_while b c p lbody s s' ws = case ws of 
  BWhlF {} -> 
    ()
  BWhlT _ _ _ _ smid _ c_s_smid w_smid_s' -> 
    lbody s smid c_s_smid &&& 
    lem_while b c p lbody smid s' w_smid_s'

    

-- In the BWhileT case, here's what I know
-- lbody     :: Legit (p `bAnd` b) c p
-- ws        :: Prop(BStep (While b c) s s')
-- c_s_smid  :: Prop(BStep c s smid)
-- w_smid_s' :: Prop(BStep (While b c) smid s')
-- s  :: {State | bval p s}
-- s' s.t. BStep (While b c) s s' has proof as above                            
-- GOAL: prove bval (p `And` Not b) s'

-- My solution:
-- lbody s smid c_s_smid :: { bval p smid } because bval p s and bval b s
--  then we can use structural induction on the proof tree `ws` deriving
--  (BStep c s s') to get
-- lem_while b c p lbody smid s' w_smid_s' :: { bval (bAnd p (Not b)) s' }
-- because { bval p smid } by the above.

-- HINT: What are `smid`, `c_s_smid` and `w_smid_s'` ? 
--       What assertion does `smid` satisfy? 
--       How can you use `smid` and `lbody` to deduce that the output state `s'` 
--       satisfies the postcondition?

--------------------------------------------------------------------------------
-- | PROBLEM 1.d: Use the above `lem_skip`, `lem_asgn`, `lem_seq` etc to prove 
--                the Soundness of Floyd-Hoare Logic 
--                The definition of `FH` is given in Axiomatic.hs
--------------------------------------------------------------------------------

{-@ thm_fh_legit :: p:_ -> c:_ -> q:_ -> FH p c q -> Legit p c q @-}
thm_fh_legit :: Assertion -> Com -> Assertion -> FH -> Legit 
thm_fh_legit p _ _ (FHSkip {})      
  = lem_skip p

thm_fh_legit _ _ q (FHAsgn _ x a) 
  = lem_asgn x a q

thm_fh_legit _ _ _ (FHSeq p c1 q c2 r p_c1_q q_c2_r) 
  = lem_seq c1 c2 p q r (thm_fh_legit p c1 q p_c1_q) 
                        (thm_fh_legit q c2 r q_c2_r)

thm_fh_legit _ _ _ (FHIf p q b c1 c2 fh_c1 fh_c2)
  = lem_if b c1 c2 p q (thm_fh_legit (bAnd p      b)  c1 q fh_c1)
                       (thm_fh_legit (bAnd p (Not b)) c2 q fh_c2)

thm_fh_legit _ _ _ (FHWhl p b c p_c_p) 
  = lem_while b c p (thm_fh_legit (bAnd p b) c p p_c_p)

thm_fh_legit _ _ _ (FHPre p' p q c p'_imp_p p_c_q)
  = lem_conseq_pre  p' p q c p'_imp_p (thm_fh_legit p c q p_c_q)

thm_fh_legit _ _ _ (FHPost p q q' c p_c_q q_imp_q')
  = lem_conseq_post p q q' c (thm_fh_legit p c q p_c_q) q_imp_q' 
