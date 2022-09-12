{-# LANGUAGE GADTs #-}

--  https://jamesrwilcox.com/InductionExercises.html

module Induction where

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

import Prelude hiding (id, sum)
import Language.Haskell.Liquid.ProofCombinators
import Data.Set (Set)
import qualified Data.Set as Set


{-@ incr :: Nat -> Nat @-}
incr :: Int -> Int
incr x = x + 1

data List = Emp | Cons Int List

{-@ reflect isSorted @-}
isSorted :: List -> Bool
isSorted Emp = True
isSorted (Cons x xs) = case xs of
                        Emp -> True
                        Cons x1 xs1 -> (x <= x1) && (isSorted xs)


{-@ reflect insert @-}
{-@ insert :: x:Int -> {xs:List | isSorted xs} -> {xs:List | isSorted xs} @-}
insert :: Int -> List -> List 
insert x Emp     = Cons x Emp
insert x (Cons y ys)
  | x <= y        = Cons x (Cons y ys)
  | otherwise     = (lem_ins y x ys) `cast` (Cons y (insert x ys))

-- min x (head ys) <= head (insert x ys)


{-@ lem_ins :: y:Int -> {x:Int | y < x} -> {ys:List | isSorted (Cons y ys)} -> {isSorted (Cons y (insert x ys))} @-}
lem_ins :: Int -> Int -> List -> Bool
lem_ins y x Emp = True
lem_ins y x (Cons y1 ys) = if y1 < x then lem_ins y1 x ys else True

{- reflect lem_ins @-}


{- 
-------------------------------------------------------------------------------
-- | Tail-Recursive Style -----------------------------------------------------
-------------------------------------------------------------------------------

{-@ reflect sumL @-}
sumL :: [Int] -> Int
sumL []     = 0
sumL (x:xs) = x + sumL xs

{-@ reflect sumTl @-}
sumTl :: [Int] -> Int
sumTl xs = sumTl' 0 xs

{-@ reflect sumTl' @-}
sumTl' :: Int -> [Int] -> Int
sumTl' acc []     = acc
sumTl' acc (x:xs) = sumTl' (acc + x) xs 

-------------------------------------------------------------------------------

{-@ thm_sum' :: acc:_ -> xs:_ -> { acc + sumL xs == sumTl' acc xs } @-}
thm_sum' :: Int -> [Int] -> ()
thm_sum' acc []     = ()
thm_sum' acc (x:xs) = thm_sum' (acc + x) xs

{-@ thm_sum :: xs:_ -> { sumL xs == sumTl xs } @-}
thm_sum :: [Int] -> ()
thm_sum = thm_sum' 0

-------------------------------------------------------------------------------
-- | Continuation Passing Style -----------------------------------------------
-------------------------------------------------------------------------------

{-@ reflect sum_cont' @-}
sum_cont' :: (Int -> a) -> [Int] -> a
sum_cont' k []     = k 0   
sum_cont' k (x:xs) = sum_cont' (cont k x) xs 

{-@ reflect cont @-}
cont :: (Int -> a) -> Int -> Int -> a 
cont k x ans = k (x + ans)

{-@ reflect id @-}
id :: Int -> Int
id x = x 

{-@ reflect sum_cont @-}
sum_cont :: [Int] -> Int
sum_cont xs = sum_cont' id xs

-------------------------------------------------------------------------------

{-@ thm_cont' :: k:_ -> xs:_ -> { sum_cont' k xs == k (sumL xs) } @-}
thm_cont' :: (Int -> Int) -> [Int] -> Proof 
thm_cont' k []     = () 
thm_cont' k (x:xs) =  sum_cont' k (x:xs)
                  === sum_cont' (cont k x) xs
                    ? thm_cont' (cont k x) xs
                  === (cont k x) (sumL xs)
                  === k (x + sumL xs) 
                  === k (sumL (x:xs)) 
                  *** QED

{-@ thm_cont :: xs:_ -> { sum_cont xs == sumL xs } @-}
thm_cont :: [Int] -> Proof
thm_cont xs = thm_cont' id xs

-------------------------------------------------------------------------------
-- Tail Recursive Fibonacci  
-------------------------------------------------------------------------------

{-@ reflect fib @-}
fib :: Int -> Int
fib n 
  | n <= 1    = 1
  | otherwise = fib (n-1) + fib (n-2)

{-@ reflect fibT' @-}
fibT' :: Int -> Int -> Int -> Int
fibT' n a b  
  | n <= 0    = b
  | otherwise = fibT' (n-1) (a + b) a

{-@ reflect fibT @-}
fibT :: Int -> Int
fibT n = fibT' n 1 1
   
--------------------------------------------------------------------------------------------------

{-@ thm_fibT' :: n:{2 <= n} -> a:_ -> b:_ -> { fibT' n a b == a * fib (n-1) + b * fib(n - 2) } @-}
thm_fibT' :: Int -> Int -> Int -> Proof
thm_fibT' 2 a b = () 
thm_fibT' n a b = thm_fibT' (n-1) (a+b) a

{-@ thm_fibT :: n:Nat -> {fibT n == fib n} @-}
thm_fibT :: Int -> Proof
thm_fibT 0 = () 
thm_fibT 1 = () 
thm_fibT n = thm_fibT' n 1 1
-}
