\begin{comment}
\begin{code}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE GADTs #-}

module Programs where

import Prelude hiding ((++))
import Language.Haskell.Liquid.ProofCombinators
import State

infixl 7 @@
infixl 3 <~

{-@ reflect <~ @-}

{-@ reflect .+. @-}
(.+.) :: AExp -> AExp -> AExp

{-@ reflect .-. @-}
(.-.) :: AExp -> AExp -> AExp


{-@ reflect .*. @-}
(.*.) :: AExp -> AExp -> AExp

{-@ reflect .&&. @-}
(.&&.) :: BExp -> BExp -> BExp

{-@ reflect .||. @-}
(.||.) :: BExp -> BExp -> BExp

{-@ reflect .=>. @-}
(.=>.) :: BExp -> BExp -> BExp

{-@ reflect .==. @-}
(.==.) :: AExp -> AExp -> BExp

{-@ reflect .!=. @-}
(.!=.) :: AExp -> AExp -> BExp

{-@ reflect .<=. @-}
(.<=.) :: AExp -> AExp -> BExp

{-@ reflect bval @-}
{-@ reflect aval @-}
\end{code}
\end{comment}

\section{Programs} \label{sec:programs}

Next, lets spell out the syntax and semantics
of \lang, that language that we wish to build
a verifier for. We will define a datatype to
represent the \emph{syntax} of \lang programs
and then formalize their \emph{semantics} by
defining evaluation functions and transition
rules.

\subsection{Syntax} \label{sec:programs:syntax}

\lang is a standard imperative language with
integer valued variables, arithmetic expressions,
boolean conditions, assignments, branches
and loops.

\mypara{Variables and Expressions}
%
\lang has (integer valued) identifiers @Id@
and arithmetic expressions @AExp@, represented
by the datatypes
%
\begin{code}
type Val = Int
type Id = String

data AExp
  = N Val           -- ^ 0,1,2...
  | V Id            -- ^ x,y,z...
  | Plus  AExp AExp -- ^ e1 + e2
  | Minus AExp AExp -- ^ e1 - e2
  | Times AExp AExp -- ^ e1 * e2
\end{code}
%
We can define infix operators
%
\begin{code}
b1 .+. b2 = Plus  b1 b2
b1 .-. b2 = Minus b1 b2
b1 .*. b2 = Times b1 b2
\end{code}
%
For example, we can represent the
expression $x + 2 * y$ as
%
\begin{code}
e0 = V "x" .+. (N 2 .*. V "y")
\end{code}


\mypara{Conditions}
%
We use relations on integer expressions
to build \emph{conditions} which can be
further combined using boolean operators
%
\begin{code}
data BExp
  = Bc  Bool       -- ^ True, False
  | Not BExp       -- ^ not b
  | And BExp BExp  -- ^ b1 && b2
  | Leq AExp AExp  -- ^ a1 <= a2
  | Eql AExp AExp  -- ^ a1 == a2
\end{code}
%
We can define other relations and boolean
operations using the above.
%
\begin{code}
e1 .==. e2 = Eql e1 e2
e1 .!=. e2 = Not (e1 .==. e2)
b1 .<=.  b2 = Leq b1 b2
b1 .<.  b2 = (b1 .<=. b2) .&&. (b1 .!=. b2)
b1 .&&. b2 = And b1 b2
b1 .||. b2 = Not (Not b1 .&&. Not b2)
b1 .=>. b2 = (Not b1) .||. b2
\end{code}

\mypara{Commands}
%
We can use @AExp@ and @BExp@
to define the syntax of \emph{commands} @Com@
%
\begin{code}
data Com
  = Skip                    -- skip
  | Assign Id    AExp       -- x <~ a
  | Seq    Com   Com        -- c1; c2
  | If     BExp  Com   Com  -- if b then c1 else c2
  | While  BExp  BExp  Com  -- while {inv} b c
\end{code}
%
We can introduce some helper functions
to improve readability, \eg
%
\begin{code}
(<~) :: Id -> AExp -> Com
x <~ e = Assign x e
\end{code}
%
The following \lang program sums
up the integers from @1@ to @n@
with the result stored in @r@
%
\begin{code}
com_sum inv =
  ("i" <~ N 0) @@                -- i <~ 0;
  ("r" <~ N 0) @@                -- r <~ 0;
  While inv (V "i" .!=. V "n")   -- WHILE (i != n)
    ("r" <~ V "r" .+. V "i") @@  --  r <~ r + i;
    ("i" <~ V "i" .+. N 1)       --  i <~ i + 1
\end{code}


\subsection{Semantics} \label{sec:programs:semantics}

Next, we the semantics of programs via \emph{states},
\emph{valuations} and \emph{transitions}.
%
% \mypara{States}
%
A \emph{state} is map from @Id@entifiers
to (integer) @Val@ues
%
\begin{spec}
type State = Map Id Val
\end{spec}
%
where a @Map k v@ is a sequence of key-value pairs,
with a @Def@ault value for missing keys
%
\begin{spec}
data Map k v = Def v | Set k v (Map k v)
\end{spec}
%
We can % create states with a @def@ault value,
@set@ the value of a variable and
@get@ the value of a variable in a state, via
%
\begin{spec}
get :: (Eq k) => Map k v -> k -> v
get (Def v)     _  = v
get (Key k v s) k' = if k == k' then v else get s k'

set :: Map k v -> k -> v -> Map k v
set s k v = Set k v s
\end{spec}
%
For example, suppose that @s0@ is the @State@
%
\begin{code}
s0 = set "y" 30 (set "x" 20 (set "y" 10 (def 0)))
\end{code}
%
Then @get "x" s0@ and @get "y" s0@ respectively evaluate
to @20@ and @30@ and @get z s0@ evaluates to @0@ for
any other identifer @z@.

\mypara{Evaluating Expressions and Conditions}
%
We can lift the notion of valuations from states to
arithmetic expressions via the function @aval@
%
\begin{code}
aval                 :: AExp -> State -> Val
aval (N n) _         = n
aval (V x) s         = get s x
aval (Plus  e1 e2) s = aval e1 s + aval e2 s
aval (Minus e1 e2) s = aval e1 s - aval e2 s
aval (Times e1 e2) s = aval e1 s * aval e2 s
\end{code}
%
For example @aval e0 s0@ evaluates to @80@
where @s0@ is the state where @"x"@ and @"y"@
were respectively @"20"@ and @"30"@ and
@e0@ is the expression representing
$x + 2 \times y$.

\mypara{Evaluating Conditions}
%
Similarly, we extend the notion of valuations
to boolean conditions via the function @bval@
%
\begin{code}
bval :: BExp -> State -> Bool
bval (Bc   b)     _ = b
bval (Not  b)     s = not (bval b s)
bval (And  b1 b2) s = bval b1 s && bval b2 s
bval (Leq  a1 a2) s = aval a1 s <= aval a2 s
bval (Eql a1 a2)  s = aval a1 s == aval a2 s
\end{code}
%
For example, is @x_lt_y = V "x" .<. V "y"@ then @bval x_lt_y s0@ is @True@.

\mypara{Transitions}
%
The execution of a @Com@mand @c@ from a state
@s@ \emph{transitions} the system to some successor
state @s'@.
%
The direct route would be to formalize transitions
as a function that takes as input a command and
input state @s@ and returns the successor @s'@
as output.
%
Unfortunately, this path is blocked by two hurdles.
%
First, the function is \emph{partial} as for certain
starting states @s@, certain commands @c@ may be
\emph{non-terminating}.
%
Second, more importantly, our Floyd-Hoare
soundness proof will require a form of
induction on the execution traces that
provide evidence of \emph{how} @s@
transitioned to @s'@.

\mypara{Big-Step Semantics}
%
Thus, we represent the transitions via the
classical \emph{big-step} (or \emph{natural})
style where $\bstep{c}{s}{s'}$ indicates that
the execution of command $c$ transitions the
machine from a state $s$ to $s'$.
%
The rules in \cref{fig:bigstep} characterize
the transitions in terms of sub-commands of $c$.
%
\rulename{B-Skip} states
that @Skip@ leaves the state unchanged
(\ie yields a transition from $s$ to $s$).
%
\rulename{B-Assign} says that
the command @Assign x e@ transitions the
system from $s$ to a new state where the
of $x$ has been set to $\texttt{aval}\ e\ s$:
the valuation of $e$ in $s$e
%
\rulename{B-Seq} says that $\texttt{Seq}\ c_1\ c_2$
transitions the system from $s$ to $s''$ if $c_1$
transitions $s$ to some $s'$ and $c_2$ transitions
$s'$ to $s''$.
%
The rules for sequencing branches
\rulename{B-If-T, B-If-F} and loops
\rulename{B-Whl-T, B-Whl-F} similarly
describe how the execution of the sub-commands
yield transitions from the respective input
states to their outputs, using $\texttt{bval}$
to select the appropriate sub-command for
conditionals.

\mypara{Reifying Transitions as a Refined Datatype}
%
We represent the big-step transition relation
$\bstep{c}{s}{s'}$ as a \emph{proposition}
@BStep c s s'@, and reify the \emph{evidence}
that establishes the transitions via the refined
datatype in \cref{fig:bigstep:code}.
%
Each rule in \cref{fig:bigstep} is formalized
by a data constructor of the corresponding name,
whose \emph{input} preconditions mirror the
hypotheses of the rule, and whose \emph{output}
establishes the postcondition.
%
For example the @BSeq@ constructor takes as input
the sub-commands @c1@ and @c2@, states @s@, @s'@
and @s''@, and evidence @BStep c1 s s'@ and
@BStep c2 s' s''@ (that @c1@ and @c2@ respectively
transition @s@ to @s'@ and @s'@ to @s''@)
to output evidence that @Seq c1 c2@ transitions @s@ to @s''@.

This reification addresses both the hurdles that block
a direct encoding via a transition function.
%
First, the evidence route sidesteps the problem of non-termination
by letting us work with \emph{derivation trees} that correspond
exactly to terminating executions.
%
Second, the trees provide a concrete object that describes
\emph{how} a state @s@ transitioned to @s'@ and now we can
do inductive proofs over traces, via recursive functions on
the derivation trees.



the transition-function is partial (due to divergence)

]totality is addressed
By reifying ication Unfortunately, this path is blocked by two hurdles.

\begin{figure}[t]
\judgementHead{Big-Step Transition}{\bstep{c}{s}{s'}}
\begin{mathpar}
\inferrule
  { }
  { \bstep{\cSkip}{s}{s} }
  { \rulename{B-Skip} }

\inferrule
  {  }
  { \bstep{\cAsgn{x}{e}}{s}{\texttt{set}\ x\ \texttt{aval}\ e\ s} }
  { \rulename{B-Assign} }

\inferrule
  {
    \bstep{c_1}{s}{s'} \and
    \bstep{c_2}{s'}{s''}
  }
  { \bstep{\cSeq{c_1}{c_2}}{s}{s''} }
  {\rulename{B-Seq}}

\inferrule
  {
    {\texttt{bval}\ b\ s} \and
    \bstep{c_1}{s}{s'}
  }
  {
    \bstep{\cIf{b}{c_1}{c_2}}{s}{s'}
  }
  {\rulename{B-If-T}}

\inferrule
  {
    {\neg \texttt{bval}\ b\ s} \and
    \bstep{c_2}{s}{s'}
  }
  {
    \bstep{\cIf{b}{c_1}{c_2}}{s}{s'}
  }
  {\rulename{B-If-F}}


\inferrule
  {
    {\neg \texttt{bval}\ b\ s}
  }
  {
    \bstep{\iWhile{I}{b}{c}}{s}{s}
  }
  {\rulename{B-While-F}}

\inferrule
  {
    {\texttt{bval}\ b\ s} \and
    \bstep{c}{s}{s'}  \and
    \bstep{\iWhile{I}{b}{c}}{s'}{s''}
  }
  {
    \bstep{\iWhile{I}{b}{c}}{s}{s''}
  }
  {\rulename{B-While-T}}
\end{mathpar}
\caption{Big-Step Transitions for \lang commands.}
\label{fig:bigstep}
\end{figure}


\begin{figure}[t]
\begin{code}
{-@  data BStep where
      BSkip ::
       s:_ -> BStep Skip s s

      BAsgn ::
       x:_ -> a:_ -> s:_ ->
       BStep (Assign x a) s (asgn x a s)

      BSeq  ::
       c1:_ -> c2:_ -> s:_ -> s':_ -> s'':_ ->
       BStep c1 s s' -> BStep c2 s' s'' ->
       BStep (Seq c1 c2) s s''

      BIfT  ::
       b:_ -> c1:_ -> c2:_ -> s:{bval b s} -> s':_ ->
       BStep c1 s s' ->
       BStep (If b c1 c2) s s'

      BIfF  ::
       b:_ -> c1:_ -> c2:_ -> s:{not (bval b s)} -> s':_ ->
       BStep c2 s s' ->
       BStep (If b c1 c2) s s'

      BWhlF ::
       i:_ -> b:_ -> c:_ -> s:{not (bval b s)} ->
       BStep (While i b c) s s

      BWhlT ::
       i:_ -> b:_ -> c:_ -> s:{bval b s} -> s':_ -> s'':_ ->
       BStep c s s' -> BStep (While i b c) s' s'' ->
       BStep (While i b c) s s''  @-}
\end{code}
\caption{Reifying the derivation of $\bstep{c}{s}{s'}$ with the refined datatype \texttt{BStep c s s'}.}
\label{fig:bigstep:code}
\end{figure}


\begin{comment}
\begin{code}
{-@ type BStep C S1 S2 = {v:_ | prop v = (BStepProp C S1 S2)} @-}

--------------------------------------------------------------------------------
-- | Arithmetic Expressions
--------------------------------------------------------------------------------
type State = GState Id Val

{-@ reflect asgn @-}
asgn :: Id -> AExp -> State -> State
asgn x a s = set x (aval a s) s

-- sub :: Id -> AExp -> AExp -> AExp
-- sub x e (Plus  a1 a2)  = Plus  (sub x e a1) (sub x e a2)
-- sub x e (Minus a1 a2)  = Minus (sub x e a1) (sub x e a2)
-- sub x e (Times a1 a2)  = Times (sub x e a1) (sub x e a2)
-- sub x e (V y) | x == y = e
-- sub _ _ a              = a

--------------------------------------------------------------------------------
-- | Boolean Expressions
--------------------------------------------------------------------------------
{-@ reflect bAnd @-}
bAnd :: BExp -> BExp -> BExp
bAnd b1 b2 = And b1 b2

{-@ reflect bIte @-}
bIte :: BExp -> BExp -> BExp -> BExp
bIte p b1 b2 = And (p .=>. b1) ((Not p) .=>. b2)

{-@ reflect bLess @-}
bLess :: AExp -> AExp -> BExp
bLess a1 a2 = And (Leq a1 a2) (Not (Eql a1 a2))

{-@ reflect bTrue @-}
bTrue :: BExp
bTrue = Bc True

{-@ reflect tt @-}
tt :: BExp
tt = Bc True

{-@ reflect ff @-}
ff :: BExp
ff = Bc False

-- {-@ reflect bsub @-}
-- bsub :: Id -> AExp -> BExp -> BExp
-- bsub x a (Bc  b)     = Bc  b
-- bsub x a (Not b)     = Not (bsub x a b)
-- bsub x a (And b1 b2) = And (bsub x a b1) (bsub x a b2)
-- bsub x a (Leq a1 a2) = Leq (sub  x a a1) (sub  x a a2)
-- bsub x a (Eql a1 a2) = Eql (sub  x a a1) (sub  x a a2)




--------------------------------------------------------------------------------
-- | IMP Commands
--------------------------------------------------------------------------------


{-@ reflect @@ @-}
(@@) :: Com -> Com -> Com
s1 @@ s2 = Seq s1 s2

--------------------------------------------------------------------------------
-- | Big-step Semantics
--------------------------------------------------------------------------------

data BStepP where
  BStepProp :: Com -> State -> State -> BStepP

data BStep where
  BSkip :: State -> BStep
  BAsgn :: Id -> AExp -> State -> BStep
  BSeq  :: Com   -> Com  -> State  -> State -> State -> BStep -> BStep -> BStep
  BIfT  :: BExp  -> Com  -> Com   -> State -> State -> BStep -> BStep
  BIfF  :: BExp  -> Com  -> Com   -> State -> State -> BStep -> BStep
  BWhlF :: BExp  -> BExp  -> Com  -> State -> BStep
  BWhlT :: BExp  -> BExp  -> Com  -> State -> State -> State -> BStep -> BStep -> BStep


{-@ reflect cmd_1 @-}
cmd_1 = Assign "x" (N 5)

{-@ reflect cmd_2 @-}
cmd_2 = Assign "y" (V "x")

{-@ reflect cmd_1_2 @-}
cmd_1_2 = cmd_1 @@ cmd_2

{-@ reflect prop_set @-}
prop_set cmd x v s = BStepProp cmd s (set x v s)

{-@ step_1 :: s:State -> Prop (prop_set cmd_1 {"x"} 5 s)  @-}
step_1 s =  BAsgn "x" (N 5) s

{-@ step_2 :: s:{State | get s "x" == 5} -> Prop (prop_set cmd_2 { "y" } 5 s) @-}
step_2 s = BAsgn "y" (V "x") s

{-@ step_1_2 :: s:State -> BStep cmd_1_2 s (set {"y"} 5 (set {"x"} 5 s)) @-}
step_1_2 s = BSeq cmd_1 cmd_2 s s1 s2 (step_1 s) (step_2 s1)
  where
    s1     = set "x" 5 s
    s2     = set "y" 5 s1
\end{code}
\end{comment}