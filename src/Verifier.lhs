\begin{comment}
\begin{code}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--diff"        @-}
{-@ infixr .=>.           @-}  -- TODO: Silly to have to rewrite this annotation!

module Verifier where

import           Language.Haskell.Liquid.ProofCombinators
import qualified State as S
import           Programs
import           FloydHoare

{-@ reflect pre @-}
{-@ reflect ic @-}
{-@ reflect vc @-}
\end{code}
\end{comment}

\section{Algorithmic Verification} \label{sec:algorithmic}

The Floyd-Hoare proof rules provide
a \emph{methodology} to determine
whether a triple is legitimate.
%
However, to do so, we must still
construct a valid derivation,
which requires us some manual
effort to
%
(1)~determine where to use the \emph{consequence} rules,
and
(2)~check that various \emph{side conditions} hold
    for loop invariants.

\subsection{Verification Condition Generation} \label{sec:vcgen}

Next, we show how to automate verification
by computing a single \emph{verification condition}
whose validity demonstrates the legitimacy
of a triple.

\mypara{Weakest Preconditions}
%
In the first step, we \emph{assume}
the side conditions hold to check if
the given pre-condition establishes
the desired post-condition, thereby
automating the application of consequence.
%
We will do so via Dijkstra's
\emph{predicate transformers}
\cite{Dijkstra75}: a function
@pre@ which given a command @c@
and a postcondition @q@ computes
an assertion @p@ corresponding to
the \emph{weakest} (\ie most general)
condition under which the @c@
is guaranteed to transition
to a state at which @q@ holds.
%
\begin{code}
pre :: Com -> Assertion -> Assertion
pre Skip          q = q
pre (Assign x a)  q = bsub x a q
pre (Seq c1 c2)   q = pre c1 (pre c2 q)
pre (If b c1 c2)  q = bIte b (pre c1 q) (pre c2 q)
pre (While i _ _) _ = i
\end{code}
%
In the above, @bIte p q r = (p .=> q) .&&. (Not p .=> r)@
and the substitution @bsub x a q@ replaces occurrences
of @x@ in @q@ with @a@.

We can verify a triple $\fht{p}{c}{q}$ by checking
the validity of the assertion @p .=>. (pre c q)@.
%
For example to check the triple
$\fht{10 \leq \texttt{x} }{ \cAsgn{\texttt{x}}{\texttt{x} + 1} }{10 \leq \texttt{x}}$
we would compute the weakest precondition $10 \leq (x + 1)$,
and then check the validity of $10 \leq x \Rightarrow 10 \leq (x + 1)$.

\mypara{Invariant Side Conditions}
%
The definition of @pre@ blithely \emph{trusts}
the invariants annotations for each @While@-loop
are ``correct'', \ie are preserved by the loop
body and suffice to establish the post-condition.
%
To make the verifier sound, in the second step
we must guarantee that the annotations are indeed
invariants, by checking them via
\emph{invariant side-conditions}
computed by the function @ic@
%
\begin{code}
ic :: Com -> Assertion -> Assertion
ic Skip          _ = bTrue
ic (Assign {})   _ = bTrue
ic (Seq c1 c2)   q = ic c1 (pre c2 q) .&&. ic c2 q
ic (If _ c1 c2)  q = ic c1 q .&&. ic c2 q
ic (While i b c) q = ((i .&&. b)     .=>. pre c i) .&&.
                     ((i .&&. Not b) .=>. q      ) .&&.
                     ic c i
\end{code}
%
In essence, @ic@ traverses the entire command to find
additional constraints that enforce that, at each loop
@While i b c@ the annotation @i@ is indeed an invariant
that can be used to find a valid Floyd-Hoare proof for @c@,
as made precise by the following lemma
%
\begin{spec}
lemIC :: c:_ -> q:_ -> Valid (ic c q) -> FH (pre c q) c q
\end{spec}
%
That is, we can prove by induction on the structure of @c@
that whenever the side-condition holds, executing command @c@
from a state @pre c q@ establishes the postcondition @q@.

\mypara{Verification Conditions}
%
We combine the weakest preconditions and invariant side conditions
into a single \emph{verification condition} @vc@ whose validity checks
the correctness of a Floyd-Hoare triple
%
\begin{code}
vc :: Assertion -> Com -> Assertion -> Assertion
vc p c q = (p .=>. pre c q) .&&. ic c q
\end{code}
%
We combine @lem_ic@ with the rule of consequence
@FHPre@ to establish that the validity of the @vc@
establishes the existence of a Floyd-Hoare proof
%
\begin{spec}
lemVC :: p:_ -> c:_ -> q:_ -> Valid (vc p c q) -> FH p c q
\end{spec}
%
We combine the above with the soundness of Floyd-Hoare derivations
@thm_fh_legit@ to show that verification conditions demonstrate
the legitimacy of triples
%
\begin{spec}
thmVC :: p:_ -> c:_ -> q:_ -> Valid (vc p c q) -> Legit p c q
\end{spec}

\subsection{Embedded Verification} \label{sec:verify}

Finally we \emph{embed} the @vc@ generation
within a typed API, turning the type
checker into a domain-specific @verify@ function
%
\begin{code}
{-@ verify :: p:_ -> c:_ -> q:_ -> Valid (vc p c q) -> () @-}
verify :: Assertion -> Com -> Assertion -> Valid -> ()
verify _ _ _ _ = ()
\end{code}
%
Only the type signature for @verify@ is interesting:
it says that @verify p c q ok@ typechecks \emph{only}
if @ok@ demonstrates the \emph{validity} of @vc p c q@,
which can be done, simply via the term @\_ -> ()@
as shown in @pf_valid@ (in \cref{sec:deductive}).
%
Lets put our embedded verifier to work, by using
it to check some simple \lang programs

\mypara{Example: Absolute Value}
%
As a first example, lets write a small branching program
that assigns @r@ to the \emph{absolute value} of @x@.
%
\begin{code}
ex_abs = verify p c q (\_ -> ())
  where
    p = bTrue

    c = If (N 0 .<=. V "x")
          ("r" <~ V "x")
          ("r" <~ N 0 .-. V "x")

    q = (N 0 .<=. V "r") .&&. (V "x" .<=. V "r")
\end{code}

\mypara{Example: Swap}
%
Here's a second example that \emph{swaps} the values
held inside @x@ and @y@ via a sequence of arithmetic
operations
%
\begin{code}
ex_swap = verify p c q (\_ -> ())
  where
    p = (V "x" .==. V "a") .&&. (V "y" .==. V "b")

    c = ("x" <~ (V "x" .+. V "y")) @@
        ("y" <~ (V "x" .-. V "y")) @@
        ("x" <~ (V "x" .-. V "y"))

    q = (V "x" .==. V "b") .&&. (V "y" .==. V "a")
\end{code}

\mypara{Example: Sum}
%
Let us conclude with an example mirroring the one
we started with in \S~\ref{sec:overview} -- a loop
that sums up the numbers from $0$ to $n$.
%
Here, we supply the loop invariant that relates the
intermediate values of \texttt{r} with the loop index
\texttt{i} to establish the post condition that states
the result holds the (closed-form value of the) summation.
%
\begin{code}
ex_sum _ = verify p c q (\_ -> ())
 where
  p   = N 0 .<=. V "n"

  c   = ("i" <~ N 0) @@
        ("r" <~ N 0) @@
        While inv (V "i" .!=. V "n") (
          ("r" <~ (V "r" .+. V "i")) @@
          ("i" <~ (V "i" .+. N 1))
        )

  q   = N 2 .*. V "r" .==. (V "n" .*. (V "n" .-. N 1))

  inv = p .&&.
        ((N 2 .*. V "r") .==. ((V "i" .-. N 1) .*. V "i"))

\end{code}
%
% rel r x = (N 2 .*. V r) .==. ((V x .-. N 10) .*. V x)
