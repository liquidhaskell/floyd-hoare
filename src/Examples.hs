--------------------------------------------------------------------------------
-- | FINAL PROBLEM 3: Loop Invariants
--------------------------------------------------------------------------------

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--diff"        @-}

{-# LANGUAGE GADTs #-}

module Examples where

import           Prelude hiding ((++)) 
import           Language.Haskell.Liquid.ProofCombinators
import qualified State as S
import           Programs
import           FloydHoare
import           Verifier 

----------------------------------------------------------------
ex1   :: () -> ()
ex1 _ = verify p c q (\_ -> ()) 
  where 
    p = tt                   -- { true } 
    c = "x" <~ (N 5)        --    x := 5
    q = (V "x") .==. (N 5)   -- { x == 5 }

----------------------------------------------------------------

ex2   :: () -> () 
ex2 _ = verify p c q (\_ -> ()) 
  where 
    p = (V "x") .==. (N 2)      -- { x = 2 } 
    c = "x" <~ (V "x" .+. N 1)  --    x := x + 1
    q = (V "x") .==. (N 3)      -- { x = 3 }

----------------------------------------------------------------

ex2a   :: () -> () 
ex2a _ = verify p c q (\_ -> ()) 
  where 
    p  = V "x" .==. N 2          -- { x = 2 } 
    c  = c1 @@ c1                --    x := x + 1 
    c1 = "x" <~ (V "x" .+. N 1)  --    x := x + 1
    q  = V "x" .==. N 4          -- { x = 4 }

----------------------------------------------------------------

ex4  :: () -> () 
ex4 _  = verify p (c1 @@ c2) q (\_ -> ()) 
  where 
    p  = tt                   -- { True } 
    c1 = "x" <~ (N 5)         --    x := 5 
    c2 = "y" <~ (V "x")       --    y := x 
    q  = (V "y") .==. (N 5)   -- { y = 5 }

----------------------------------------------------------------
ex5  :: () -> () 
ex5 _ = verify p c q (\_ -> ()) 
  where 
    p = (V "x" .==. N 2) .&&. (V "x" .==. N 3) -- { x = 2 && x = 3} 
    c = "x" <~ N 5                             --    x := 5
    q = V "x" .==. N 0                         -- { x = 0}

----------------------------------------------------------------

ex8  :: () -> () 
ex8 _ = verify p c q (\_ -> ()) 
  where 
    p = tt                  -- { true } 
    c = While (tt) tt Skip --    WHILE_i true SKIP 
    q = ff                  -- { false }
    i = tt                  -- TODO: In class

----------------------------------------------------------------

ex9  :: () -> () 
ex9 _ = verify p c q (\_ -> ()) 
  where 
    p = (V "x" .==. N 0)             -- { x = 0 } 
    c = While i (V "x" .<=. N 0)    --   WHILE_i (x <= 0) DO
          ("x" <~ (V "x" .+. N 1))   --     x := x + 1
    q = V "x" .==. N 1               -- { x = 1 } 
    i = undefined -- TODO: In class

----------------------------------------------------------------
ex10  :: () -> () 
ex10 _ = verify p c q (\_ -> ()) 
  where 
    p = (V "x" .==. N 1)                    -- { x = 1 } 
    c = While i (Not (Leq (V "x") (N 0)))     --   WHILE_i not (x <= 0) DO
          ("x" <~ (V "x" .+. N 1))            --     x := x + 1
    q = (V "x" .==. N 100)                  -- { x = 100 } 
    i = undefined -- TODO: In class

-------------------------------------------------------------------------------
-- | Example 1: branching
-------------------------------------------------------------------------------

bx1 :: () -> () 
bx1 _ = verify p c q (\_ -> ()) 
  where 
    p = tt                                     -- { true } 
    c = If (V "x" .==. N 0)              --   IF x == 0 
            ("y" <~ (N 2))                --     THEN y := 2
            ("y" <~ (V "x" .+. N 1)) --     ELSE y := x + 1
    q = (V "x" .<=. V "y")                    -- { x <= y } 

-------------------------------------------------------------------------------
-- | Example 2: Swapping Using Addition and Subtraction 
-------------------------------------------------------------------------------

bx2 :: () -> () 
bx2 _ = verify p c q (\_ -> ()) 
  where 
    p = (V "x" .==. V "a") .&&. (V "y" .==. V "b")  -- { x = a && y = b } 
    c = ("x" <~ (V "x" .+. V "y")) @@               --   x := x + y
        ("y" <~ (V "x" .-. V "y")) @@               --   y := x - y
        ("x" <~ (V "x" .-. V "y"))                  --   x := x - y
    q = (V "x" .==. V "b") .&&. (V "y" .==. V "a")  -- { x = a && y = b } 

-------------------------------------------------------------------------------
-- | Example 4: Reduce to Zero  
-------------------------------------------------------------------------------

bx4 :: () -> () 
bx4 _ = verify p c q (\_ -> ()) 
  where 
    p = tt                          -- { true } 
    c = While i (V "x" .!=. N 0)    --   WHILE not (x == 0) DO: 
          ("x" <~ (V "x" .-. N 1))  --     x := x - 1
    q = (V "x" .==. N 0)            -- { x = 0 } 
    i = tt 


----------------------------------------------------------------------------------
-- | PROBLEM 3.a : What loop `inv` lets us `verify` the following triple?
----------------------------------------------------------------------------------

problem3a   :: () -> () 
problem3a _ = verify p c q (\_ -> ())
  where 
    p   = (V "x" `Eql` V "a")                            -- { x == a } 

    c   = Assign "y" (N 0) `Seq`                         -- y := 0;
          While inv (Not (V "x" `Eql` N 0))             -- WHILE (x != 0)
            (Assign "x" ((V "x") `Minus` (N 1))  `Seq`   --   x := x - 1;
             Assign "y" ((V "y") `Plus`  (N 1)))          --   y := y + 1

    q   = (V "y" `Eql` V "a")                            -- { y == a }

    inv = (Eql (Plus (V "x") (V "y")) (V "a"))

-- pre c q == pre ( y:=0; IWhile inv _ _) q 
--         == pre (y := 0) (pre (IWhile inv _ _) q)
--         == pre (y := 0) inv 
--         == inv[0/y]

-- A correct invariant I for the loop is one such that `vc' p c q` is valid, in 
-- other words all of the following must hold:
-- 1) p => pre c q,	i.e.	(x == a) => I[0/y]	
-- 2) I and b => I, 	i.e.	(I and x!= 0) => I
-- 3) I and not b => q 	i.e.	(I and x==0) => y==a
-- It's clear that the loop preserves the sum of x and y, but we have no way to 
-- talk about their values before and after. So using what's true before we ever
-- encounter the WHILE loop, take I to be x + y == a. It's easily seen that this 
-- satisfies all of (1),(2),(3) so the verification will pass.

-- HINT: It may be faster to try "candidate" invariants using DAFNY 
--         https://rise4fun.com/Dafny/EX35 
--       Try to get DAFNY to accept that program after replacing the line 
--         invariant true;
--       with a better loop invariant i.e. other than 'true' and then plug that in for `inv`

----------------------------------------------------------------------------------
-- | PROBLEM 3.b : What loop `inv` lets us `verify` the following triple?
----------------------------------------------------------------------------------

problem3b   :: () -> () 
problem3b _ = verify p c q (\_ -> ())
  where 
    p   = (V "n" `Eql` (N 10))                                  -- { n == 10 } 

    c   = Assign "i" (N 0) `Seq`                                --   i := 0;
          Assign "r" (N 0) `Seq`                                --   r := 0;
          While inv (Not (V "i" `Eql` V "n"))                  --   WHILE (i != n)
            ( Assign "r" (V "r" `Plus` V "i") `Seq`             --     r := r + i;
              Assign "i" (V "i" `Plus` N 1)                      --     i := i + 1
            )
    q   = (V "r" `Eql` (N 45))                                  -- { r == 45 }

    inv = (And (Eql (Times (Minus (V "i") (N 1)) (V "i")) (Times (N 2) (V "r"))) 
               (Eql (V "n") (N 10)))

-- pre c q == pre ( i := 0; r := 0; IWhile inv _ _) q 
--         == pre (i := 0) (pre (r := 0) (pre (IWhile inv _ _) q))
--         == pre (i := 0) (pre (r := 0) inv)
--         == pre (i := 0) inv[0/r]
--         == inv[0/r][0/i]

-- By inspection, the code will give r the final value \sum_{i=0}^{n-1}, but that
-- doesn't help with an invariant. However, after any iteration of the loop, r holds
-- the value of the sum of integers 1 + ... + i-1. By definition of the empty sum to be
-- zero, this holds on initial entry too. Expressing this in closed form, I arrive at
-- my first attempt for the invariant. Take I = ((i-1)*i == 2*r) 
--
-- A correct invariant I = pre c q is one such that vc' p c q, in other words
-- all of the following:
-- 1) p => (pre c q), 	i.e.	(n == 10) => I[0/r][0/i]
-- 2) I and b => I, 	i.e.	(I and i != n) => I
-- 3) I and not b => q 	i.e.	(I and i == n) => r==45
--
-- This I satisfies (2) clearly and also (1) because i==0 and r==0, so both sides of I 
-- are zero. However we don't have (3) without further inferences: 
--    (i*(i-1) == 2*r) and (i==n) ==/=> r == 45
-- the above is not valid because we don't know anything about any other assignments that
-- aren't included in the invariant or in the negation of the `b` clause in the loop test.
-- So to get that r = 45 at the end we need that i = 10 at the end, or equivalently that
-- n = 10 throughout the program.
--
-- Thus my final choice of invariant is I = (i*(i-1) == 2*r) AND (n == 10) which satisfies
-- all of (1)-(3) above.

-- HINT: It may be faster to try "candidate" invariants using DAFNY 
--         https://rise4fun.com/Dafny/VowP
--       Try to get DAFNY to accept that program after replacing the line 
--         invariant true;

ex_sum :: () -> () 
ex_sum _ = verify p c q (\_ -> ())
 where 
  p   = V "n" .==. N 10                 

  c   = ("i" <~ N 0) @@                 
        ("r" <~ N 0) @@                 
        While inv (V "i" .!=. V "n") (     
          ("r" <~ (V "r" .+. V "i")) @@
          ("i" <~ (V "i" .+. N 1))
        )     
          
  q   = V "r" .==. N 45

  inv = (((V "i" .-. N 1) .*. V "i") .==. (N 2 .*. V "r")) 
        .&&. ((V "n" .==. N 10))

