


\begin{comment}
\begin{code}

{-# LANGUAGE GADTs #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Refinements where

import Prelude hiding (id, sum)
import         Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.Liquid.GHC.API (stateHackOneShot)

sum    :: Int -> Int
assert :: Bool -> ()
{-@ sumTR  :: Nat -> Int @-}
{-@ sumTR' :: Nat -> Int -> Int @-}
type Nat = Int
thm_sumTR :: Int -> Proof
lem_sumTR :: Int -> Int -> Proof
{-@ reflect sum @-}

data ReachEv a where
  Self :: Edge a -> a -> ReachEv a
  Step :: Edge a -> a -> a -> a -> ReachEv a -> ReachEv a

data ReachProp v where
  ReachProp :: Edge v -> v -> v -> ReachProp a

reachTrans :: Edge a -> a -> a -> a -> ReachEv a -> ReachEv a -> ReachEv a

{-@ type Reach E X Y = {v:_ | prop v = ReachProp E X Y } @-}
\end{code}
\end{comment}

\section{Refinement Types}\label{sec:overview}

Lets begin with a brisk introduction to refinement types
that illustrates how they can be used to formally specify
and verify properties of programs.

\subsection{Refinements}

A \emph{refinement type} a plain type like @Int@
or @Bool@ decorated by a logical predicate which
restricts the \emph{set of values}.
%
For example, the refinement type @Nat@ defined as
%
\begin{spec}
type Nat = {v:Int|0 <= v}
\end{spec}
%
denotes the set of non-negative @Int@eger values.

\mypara{Specification}
%
Consider the function @sum n@ which computes $1 + \ldots + n$
%
\begin{code}
{-@ sum :: n:Nat -> {v:Int|n <= v}  @-}
sum n = if n == 0 then 0 else n + sum (n - 1)
\end{code}
%
The signature for @sum@ is a refined \emph{function}
type that specifies:
%
(1)~A \emph{pre-condition} that @sum@ only be called with
    non-negative inputs @n@, (as otherwise it diverges), and
%
(2)~A \emph{post-condition} that states that the output
    produced by the function is no smaller than @n@.

Under classical \emph{strict} or \emph{call-by-value}
evaluation semantics (where a function's arguments must
be evaluated before the call proceeds) refinement types
represent \emph{safety} properties, \ie they correspond
to the classic notion of \emph{partial correctness}.
%
That is, the output type only specifies that \emph{if}
a value is returned, it will exceed the input @n@.
%
\emph{Lazy} evaluation muddies the waters
introducing an unexpected intertwining of safety and
termination \cite{Vazou14}.
%
For simplicity, we will assume that that the underlying
language follows the usual strict semantics, and not
concern ourselves with termination.

\mypara{Verification}
%
Refinement type checking algorithmically
verifies the implementation of @sum@
meets its specification by
%
(1)~computing a logical formula called a \emph{verification condition} (VC)
%
(2)~and then using an SMT solver to check the \emph{validity} of the VC \cite{JhalaVazou21}.
%
For @sum@ the VC is the formula that combines the assumption $0 \leq n$
from the precondition to establish that the returned values $v = 0$ and
$v = n + \mathit{sum}(n-1)$ in each branch are indeed greater than $n$.
In the latter case, the assumption $n-1 \leq \mathit{sum}(n-1)$
is established by ``inductively'' assuming the post-condition
of @sum@ for the recursive call.
%
\begin{align*}
\forall n, v.\ 0 \leq n \Rightarrow
  &\ n =       0 \Rightarrow v = 0 \Rightarrow n \leq v\ \wedge \\
  &\ n \not =  0 \Rightarrow n - 1 \leq \mathit{sum}\ (n-1) \Rightarrow v = n + \mathit{sum} (n-1) \Rightarrow n \leq v
\end{align*}

\mypara{Assertions}
%
We can encode \emph{assertions} as function calls
by defining a function that requires its input be
a @Bool@ that is @True@
%
\begin{code}
{-@ assert :: {b:Bool|b} -> () @-}
assert b = ()
\end{code}
%
Subsequent refinement type checking then statically
verifies classical assertions
%
\begin{code}
checkSum1 = assert (1 <= sum 1)
\end{code}

\subsection{Reflection} \label{sec:overview:reflection}

Refinement type checking is \emph{modular}, which means
that at call-sites, the only information known about
a function is \emph{shallow}, namely that which is stated
in its type specification.
%
Consequently, the following assertion fails to verify
%
\begin{code}
checkSum2 = assert (3 <= sum 2)
\end{code}
%
The only information about the call @sum 2@ is that
encoded in its type specification: that the output
exceeds $2$, and so @checkSum2@ fails to verify due
the \emph{invalid} VC
%
$$2 \leq \mathit{sum}(2) \Rightarrow 3 \leq \mathit{sum}(2)$$

\mypara{Reflecting Implementations into Specifications}
%
To prove \emph{deeper} properties about @sum@ we can reflect
the implementation (\ie definition) of the function into its
specification. To do so, the programmer writes
|{-@ reflect sum @-}| which \emph{strengthens}
the specification of @sum@ to
%
|$n$:Nat $\rightarrow$ {$v$:$n \leq v$ $\wedge$ $\phisum{n}{v}$}|
%
where
%
$$\phisum{n}{v} \ \doteq\ (v = \mathit{sum}(n)) \ \wedge\
                       (n = 0 \Rightarrow v = 0)\ \wedge\
                       (n \not = 0 \Rightarrow v = n + \mathit{sum}(n-1))$$

\mypara{Logical Evaluation}
%
To ensure that validity checking remains
\emph{decidable}, $\mathit{sum}$
is \emph{uninterpreted} in the
refinement logic.
%
This means, that the new VC for @checkSum@
%
$$ \forall b.\ 2 \leq \mathit{sum}(2) \wedge \phisum{2}{\mathit{sum}(2)} \Rightarrow b \Leftrightarrow (3 \leq \mathit{sum}(2)) \Rightarrow b $$
%
is still \emph{invalid} as there is no information about $\mathit{sum}(1)$.
%
Fortunately, the method of \emph{Proof by Logical Evaluation} (PLE) \cite{Vazou18}
lets the SMT solver strengthen the hypotheses by \emph{unfolding the definition}
of @sum@ to yield the following valid VC that verifies @checkSum2@.
%
$$\phisum{0}{\mathit{sum}(0)} \wedge  \phisum{1}{\mathit{sum}(1)} \wedge 2 \leq \mathit{sum}(2) \wedge \phisum{2}{\mathit{sum}(2)} \Rightarrow 3 \leq \mathit{sum}(2)$$

\mypara{Proofs by Induction}
%
Reflection and logical evaluation let us specify and verify
more interesting properties about @sum@. For example, consider
the following \emph{tail-recursive} version which can be compiled
into an efficient loop
%
\begin{code}
{-@ reflect sumTR' @-}
sumTR' :: Nat -> Int -> Int
sumTR' n a = if n == 0 then a else sumTR' (n-1) (a+n)

{-@ reflect sumTR @-}
sumTR :: Nat -> Int
sumTR n = sumTR' n 0
\end{code}
%
We can now specify that @sumTR@ is \emph{equivalent} to @sum@
by first establishing that
%
\begin{align}
\forall n, a. & \ 0 \leq n\ \Rightarrow\ \texttt{sumTR'}(n, a) = a + \texttt{sum}(n) \label{eq:sum:lem} \\
\intertext{and then using the lemma to prove that}
\forall n. & \ 0 \leq n\ \Rightarrow\ \texttt{sumTR}(n) = \texttt{sum}(n) \label{eq:sum:thm}
\end{align}

\mypara{Proofs as Programs}
%
Our approach uses the
Curry-Howard correspondence
\cite{Wadler15} to encode
logical \emph{propositions}
as refinement types, and
provide \emph{proofs} of
the propositions by writing
functions of the appropriate type.
%
Briefly, Curry-Howard shows how
universally quantified propositions
$\forall x:\texttt{Int}.\ P(x)$
correspond to the function type
@x:Int -> {P(x)}@, and that code
implementing the above type is a
constructive proof of the original
proposition.
%
For example, the proposition \cref{eq:sum:lem}
is specified and verified by
%
\begin{code}
{-@ lem_sumTR :: n:Nat -> acc:Int -> {sumTR' n acc = acc + sum n} @-}
lem_sumTR 0 _   = ()
lem_sumTR n acc = lem_sumTR (n - 1) (acc + n)
\end{code}
%
At a high-level, the the method of logical
evaluation is able to verify the above code
by using the post-condition from the recursive
invocation of @lem_sumTR@ (that ``adds'' the
induction hypothesis as an antecedent of the VC)
and automatically unfolding the definitions
of @sumTR'@ and @sum@.
%
Similarly, we translate \cref{eq:sum:thm} and prove
that it is a corollary of \cref{eq:sum:lem}
by ``calling'' the lemma (function) with the
appropriate arguments.
%
\begin{code}
{-@ thm_sumTR :: n:Nat -> { sumTR n == sum n } @-}
thm_sumTR n = lem_sumTR n 0
\end{code}

\subsection{Reification}

Some proofs require the ability to
\emph{introspect on the evidence}
that establishes why some proposition
holds.
%
As a textbook example, let us recall
the notion of the \emph{reachability}
in a graph.
%
Let $V$ and $E \subset V \times V$ denote
the set of \emph{vertices} and \emph{directed edges}
of a directed graph.
%
We say that a vertex $u$ \emph{reaches} $v$
if either (a) $u = v$ or (b) $(u, v) \in E$
and $v$ reaches $w$.
%
%\mypara{Reachability is Transitive}
%
Suppose that we wish to prove that the
notion of reachability is \emph{transitive},
\ie if $u$ reaches $v$ and $v$ reaches $w$
then $u$ reaches $w$.
%
To prove the above property, it is not enough
to know \emph{that} $u$ reaches $v$ and $v$
reaches $w$.
%
Instead, we need additional evidence: a ``path''
that describes \emph{how} the evidence
was established.

Our third key piece of machinery is a way to
\emph{reify} such evidence using data types
that can be introspected and manipulated to
provide evidence that establishes new properties.
%
This machinery corresponds to the notion of \emph{inductive}
propositions or predicates used by proof assistants like Coq
or Isabelle \cite{coq-book,NPW2002}.
%
As an example, lets see how to formalize
the notion of reachability.
%
Suppose that we represent the directed edge
relation as a predicate over vertices |v|
%
\begin{code}
type Edge v = v -> v -> Bool
\end{code}

\mypara{Step 1: Propositions as Data}
%
We encode reachability as a relation
$\reach{e}{x}{y}$ that says
$x$ reaches $y$ following
the edges $e$.
%
We can represent this relation as
proposition: a \emph{value} |Reach e u v|
that denotes that |u| reaches |v| following
the edges |e|.

\mypara{Step 2: Evidence as Data}
%
We can specify reachability via two rules
%
\begin{mathpar}
\inferrule
  { \ }
  {\reach{e}{x}{x}}
  {\rulename{Self}}

\inferrule
  {
    (x,y) \in e \and
    \reach{e}{y}{z}
  }
  { \reach{e}{x}{z} }
  {\rulename{Step}}
\end{mathpar}
%
We can formally represent
the \emph{evidence} of
reachability as a refined
datatype whose constructors
correspond to the informal rules.
%
\begin{code}
{-@ data ReachEv a where
      Self :: e:Edge a -> x:a ->
              Reach e x x
      Step :: e:Edge a -> x:a -> y:{a|e x y} -> z:a ->
              Reach e y z ->
              Reach e x z
  @-}
\end{code}
%
Following the Curry-Howard correspondence,
%
(1)~the universally quantified variables
    of the rules become input \emph{parameters}
    for the constructor,
%
(2)~the antecedents of each rule are translated
    to \emph{preconditions} for the corresponding
    constructor, and
%
(3)~ the consequent of each rule is translated
     into the \emph{postcondition} for the constructor.
%
The above datatype says there are exactly two ways
to \emph{construct} evidence of reachability:
%
(1)~|Self e x| is evidence that a vertex |x|
    can reach \emph{itself} following the
    edge-relation |e|;
%
(2)~|Step e x y z yz| uses the fact that
%
    (a)~|x| has an edge to |y| (established by the
    precondition |e x y|) and
%
    (b)~|y| reaches |z| (established by |yz| which is
    evidence that |Reach e y z|)
%
to construct evidence that |x| reaches |z|.
%
Note that the above are the \emph{only} ways to provide
evidence of reachability (\ie to construct values that
demonstrate the proposition |Reach e x y|).

\mypara{Step 3: Consuming and Producing Evidence}
%
Finally, we can prove properties about reachability,
simply by writing functions that consume and produce
evidence. For example, here is a proof that reachability
is transitive.
%
\begin{code}
{-@ reachTrans :: e:Edge a -> x:a -> y:a -> z:a ->
              Reach e x y -> Reach e y z ->
              Reach e x z  @-}
reachTrans e x y z (Self _ _) yz          = yz
reachTrans e x y z (Step _ _ x1 _ x1y) yz = Step e x x1 z x1z
  where x1z = reachTrans e x1 y z x1y yz
\end{code}
%
The \emph{specification} of @reachTrans@ represents the proposition
that reachability is transitive: for any edge relation |e|
and vertices |x,y,z| if we have evidence that |x| reaches |y|
and that |y| reaches |z| then we can construct evidence
that |x| reaches |z|.
%
The \emph{implementation} of @reachTrans@ demonstrates
the claim via code that explicitly constructs the evidence
via recursion, \ie by induction on the path from |x| to |y|.
%
In the base case, that path is empty as |x| equals |y|, in which
case the evidence |yz| that shows |y| reaches |z| \emph{also}
shows |x| reaches |z|.
%
In the inductive case, the path from |x| to |y| goes via the edge
from |x| to |x1| followed by a path |x1y| from |x1| to |y|.
(As when proving @thm_sumTR@) we \emph{apply} the induction hypothesis
by recursively ``calling'' @reachTrans@ on the sub-paths |x1y| and |yz|
to obtain evidence that |x1| reaches |z|, and then link that evidence
the edge from |x| to |x1| (\ie |Step e x x1|) to construct
the path from |x| to |z|.
%
(The termination checker automatically verifies
that the recursion in @reachTrans@, and hence
the induction, is well-founded \cite{Vazou18}.)
