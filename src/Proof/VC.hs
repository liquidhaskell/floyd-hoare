---------------------------------------------------------------------------------
-- | PROBLEM 2: Soundness of Verification Conditions. We will prove that 
--              if the `vc p c q` is valid, then the triple {p} c {q} is legit.
---------------------------------------------------------------------------------

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

{-# LANGUAGE GADTs #-}

module Proof.VC where

import           Prelude hiding ((++)) 
import           Language.Haskell.Liquid.ProofCombinators
import qualified State as S
import           Programs
import           FloydHoare 
import           Verifier
import           Proof.FH

---------------------------------------------------------------------------------
-- | PROBLEM 2.a: Complete the following lemma relating `vc` and `pre`.
--------------------------------------------------------------------------------

-- HINT: Notice that the proof is "by induction" on the `Com`, returning for each 
--       case of `Com`, the corresponding `FH` proof tree. Make sure you understand 
--       the proofs for the `ISkip`, `IAssign` and `IIf` cases before proceeding.

{-@ lem_ic :: c:_ -> q:_ -> Valid (ic c q) -> (FH (pre c q) c q) @-}
lem_ic :: Com -> Assertion -> Valid -> FH 

lem_ic Skip          q _ = FHSkip q

lem_ic (Assign x a)  q _ = FHAsgn q x a 

{- let p1 = pre c1 q 
       p2 = pre c2 q 
       p  = bIte b p1 p2 
       
    [lem_valid]    [lem_ic c1 q v]                  [lem_valid]      [lem_ic c2 q v]
    -------------  ----------------                 --------------   ---------------- 
    |- p&b => p1   |- {p1} c1 {q}                   |- p&!b => p2    |- {p2} c2 {q}
    ------------------------------ [FHPre]       ------------------------------ [FHPre]
    |- {p&b} c1 {q}                                 |- {p&!b} c2 {q}
    ------------------------------------------------------------------------------ [FHIf]
    |- { p } If b c1 c2 { q }

 -}

lem_ic (If b c1 c2)  q v = FHIf p q b (c1) (c2) pb_c1_q pnotb_c2_q 
  where 
    p                     = bIte b p1 p2 
    p1                    = pre c1 q 
    p2                    = pre c2 q 
    p1_c1_q               = lem_ic c1 q v 
    p2_c2_q               = lem_ic c2 q v 
    pb_c1_q               = FHPre (bAnd p b)       p1 q c1 v1 p1_c1_q
    pnotb_c2_q            = FHPre (bAnd p (Not b)) p2 q c2 v2 p2_c2_q
    v1                    = lem_valid_imp  b p1 p2
    v2                    = lem_valid_imp' b p1 p2

{- HINT: 

   let p = pre c1 q 
       q = pre c2 r
    
    [lem_ic c1 q v]  [lem_ic c2 r v]
    ---------------  ----------------
    |- {p} c1 {q}    |- {q} c2 {r}
    ------------------------------------[FHSeq]
    |- {p} c1;c2 {r}

 -}

lem_ic (Seq c1 c2)   r v = FHSeq p c1 q c2 r p_c1_q q_c2_r 
  where
    p                     = pre c1 q
    q                     = pre c2 r
    p_c1_q                = lem_ic c1 q v
    q_c2_r                = lem_ic c2 r v 

{- 

    ---------------------- [v]   ------------------- [lem_ic c i v]
    |- (i & b) => pre c i        |- {pre c i} c {i}
    ------------------------------------------------ [FHPre] 
    |- {i & b} c {i}
    -------------------------- [FHWhl]    ---------------- [v]
    |- {i} while b c {i & ~b}               |- (i & ~b) => q 
    -------------------------------------------------------- [FHPost]
    |- {i} while b c {q} 

    ib_c_i    = FHPre (bAnd i b) (pre c i) i c_ v (lem_ic c i v)
    i_w_inotb = FHWhl i b c_ ib_c_i
    i_w_q     = FHPost i (bAnd i (Not b)) (While b c_) v 

 -}

lem_ic (While i b c) q v = i_w_q
  where
    ib_c_i    = FHPre (bAnd i b) (pre c i) i c v (lem_ic c i v)
    i_w_inotb = FHWhl i b c ib_c_i
    i_w_q     = FHPost i (bAnd i (Not b)) q (While i b c) i_w_inotb v 


----------------------------------------------------------------------------------
-- helper lemmas used for `IIf` case, you can ignore them for `ISeq` and `IWhile`

{-@ lem_valid_imp :: b:_ -> p1:_ -> p2:_ -> (Imply (bAnd (bIte b p1 p2) b) p1) @-}
lem_valid_imp :: BExp -> BExp -> BExp -> Valid 
lem_valid_imp b p1 p2 = \_ -> () 

{-@ lem_valid_imp' :: b:_ -> p1:_ -> p2:_ -> (Imply (bAnd (bIte b p1 p2) (Not b)) p2) @-}
lem_valid_imp' :: BExp -> BExp -> BExp -> Valid 
lem_valid_imp' b p1 p2 = \_ -> () 

---------------------------------------------------------------------------------
-- | PROBLEM 2.b: Use `thm_fh_legit` and `lem_ic` to prove that `vc` is "sound"
--------------------------------------------------------------------------------

{-@ thm_ic :: c:_ -> q:_ -> Valid (ic c q) -> Legit (pre c q) c q @-}
thm_ic :: Com -> Assertion -> Valid -> Legit 
thm_ic c q v = thm_fh_legit (pre c q) c q (lem_ic c q v)


-- | Lets extend `vc` to check triples `{p} c {q}`, by generating a `vc p c q` defined 

{-@ reflect vc @-}
vc :: Assertion -> Com -> Assertion -> Assertion 
vc p c q = (p .=>. (pre c q)) .&&. (ic c q) 


--------------------------------------------------------------------------------
-- | PROBLEM 2.c: Prove that `vc` is sound, that is, that 
--                the validity of `vc p c q` implies `{p} c {q}` is legit
--------------------------------------------------------------------------------

{- HINT: here's a proof tree 

   [v]                      [lem_ic c q v]
   ---------------          ------------------
   |- p => pre c q          |- {pre c q} c {q} 
   ------------------------------------------- [FHPre]
   |- {p} c {q}

 -}

{-@ lem_vc :: p:_ -> c:_ -> q:_ -> Valid (vc p c q) -> (FH p c q) @-}
lem_vc :: Assertion -> Com -> Assertion -> Valid -> FH 
lem_vc p c q v = FHPre p (pre c q) q c v (lem_ic c q v)
-- v :: Valid ( bAnd (p => pre c q) (vc c q))

{-@ thm_vc :: p:_ -> c:_ -> q:_ -> Valid (vc p c q) -> Legit p c q @-}
thm_vc :: Assertion -> Com -> Assertion -> Valid -> Legit 
thm_vc p c q v = thm_fh_legit p c q (lem_vc p c q v)

-- HINT: This is very similar to how you used `lem_ic` to prove `thm_vc` ...
