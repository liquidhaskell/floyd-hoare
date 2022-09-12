\begin{comment}
\begin{code}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ infixr ++             @-}  -- TODO: Silly to have to rewrite this annotation!
{-@ infixr <~             @-}  -- TODO: Silly to have to rewrite this annotation!
{-@ infixr .=>.           @-}  -- TODO: Silly to have to rewrite this annotation!
{-@ infixr .==.           @-}  -- TODO: Silly to have to rewrite this annotation!
{-@ infixr .<=.           @-}  -- TODO: Silly to have to rewrite this annotation!
{-@ infixr .&&.           @-}  -- TODO: Silly to have to rewrite this annotation!

--------------------------------------------------------------------------------
-- | Inspired by
--     http://flint.cs.yale.edu/cs428/coq/sf/Hoare.html
--     http://flint.cs.yale.edu/cs428/coq/sf/Hoare2.html
--------------------------------------------------------------------------------

{-# LANGUAGE GADTs #-}

module FloydHoare where

import           Prelude hiding ((++))
import           Language.Haskell.Liquid.ProofCombinators
import qualified State as S
import           Programs

{-@ reflect cond_x_10_5 @-}
pf_valid :: State -> Proof

{-@ reflect sub @-}
{-@ reflect bsub @-}

\end{code}
\end{comment}

\section{Deductive Verification} \label{sec:deductive}

Next, let us build (and verify!)
a \emph{deductive} verifier for
\lang using the classical method
of Floyd-Hoare (FH) logic \cite{Floyd67,Hoare69}
and show how to prove it sound.

\subsection{Floyd-Hoare Triples}\label{sec:deductive:triples}

\mypara{Assertions}
%
An \emph{assertion} is a boolean condition over the program
identifiers.
%
\begin{code}
type Assertion = BExp
\end{code}
%
An assertion @p@ \emph{holds} at a state @s@
if @bval p s@ is @True@, \ie the assertion
evaluates to @True@ at the state.
%
For example, the assertion @b0 = V "x" .<. V "y"@
holds at @s0@ where @get s0 "x"@ and @get s0 "y"@
were respectively @20@ and @30@.

\mypara{Validity}
%
An assertion @p@ is \emph{valid}
if it holds \emph{for all} states,
\ie $\forall s. \texttt{bval}\ \texttt{p}\ s = \texttt{True}$.
%
Following the Curry-Howard correspondence,
we can formalize validity as
%
\begin{code}
{-@ type Valid P = s:State -> {bval P s} @-}
\end{code}
%
Logical evalation \cite{Vazou18} makes it
easy to check validity simply by refinement
typing.
%
For example, we can establish the assertion
%
\begin{code}
cond_x_10_5 = (N 10 .<=. V "x") .=>. (N 5 .<=. V "x")
\end{code}
%
is valid, simply by writing
%
\begin{code}
{-@ pf_valid :: Valid cond_x_10_5 @-}
pf_valid = \_ -> ()
\end{code}
%
Logical evaluation discharges the typing obligation
via the SMT validated VC
%
$$ \forall s.\ 10 \leq \vget{x}{s} \Rightarrow 5 \leq \vget{x}{s}$$

\mypara{Floyd-Hoare Triples}
%
A \emph{Floyd-Hoare triple} $\fht{p}{c}{q}$
comprising a \emph{precondition} $p$,
command $c$ and \emph{post-condition} $q$.
%
The triple states that if the command $c$
transitions the system \emph{from} a state $s$
where the precondition $p$ holds, \emph{to} a state $s'$,
then the postcondition $q$ holds on $s'$.

\mypara{Legitimacy of Triples}
%
We say a triple is \emph{legitimate},
written $\legit{p}{c}{q}$ if
%
$$\legit{p}{c}{q} \ \doteq\ \forall s, s'. \texttt{bval}\ p\ s \Rightarrow \bstep{c}{s}{s'} \Rightarrow \texttt{bval}\ q\ s'$$
%
We can use the Curry-Howard correspondence
to formalize the above notion as:
%
\begin{code}
{-@ type Legit P C Q =
      s:{bval P s} -> s':_ -> BStep C s s' -> {bval Q s'} @-}
\end{code}
%
We can specify and verify the triple
$\fht{0 \leq x}{ \cAsgn{y}{x + 1} }{1 \leq y}$
as
%
\begin{code}
y_x_1 :: Com
y_x_1 = ("y" <~ V "x" .+. N 1)

{-@ leg_y_x_1 :: Legit (N 0 .<=. V {"x"}) y_x_1 (N 1 .<=. V {"y"}) @-}
leg_y_x_1 :: Legit
leg_y_x_1 s s' BAsgn {} = ()
\end{code}
%
Note that evidence for the big-step transition @BAsgn {}@
tells us that the final state @s'@ is obtained by @set@ting
the value of @y@ to @1@ + the value of @x@ in the initial
state @s@.
%
Thus, refinement typing verifies legitimacy by generating
the following VC for @leg_y_x_1@ (simplified after
logical evaluation unfolds the definition of @bval@
for the pre- and post-conditions)
%
$$ \forall s, s'.\ 0 \leq \vget{x}{s}\ \Rightarrow\ s' = \vset{y}{1 + \vget{x}{s}}{s}\ \Rightarrow\ 1 \leq \vget{y}{s'}$$
%
PLE then further unfolds the definition of @set@
to allow the SMT solver to automatically verify
the VC and hence, check legitimacy.

As a second example, let @x20_y30@ be a command that sequentially
assigns @x@ and @y@ to @20@ and @30@ respectively:
%
\begin{code}
x20_y30 = ("x" <~ N 20) @@ ("y" <~ N 30)
\end{code}
%
We can verify that $\legit{\mathit{true}}{\cXY}{x \leq y}$ as
%
\begin{code}
{-@ legXY :: Legit bTrue x20_y30 (V {"x"} .<=. V {"y"}) @-}
legXY s s'' (BSeq _ _ _ _ _ (BAsgn {}) (BAsgn {})) = ()
\end{code}
%
Here, the ``pattern-matching'' on the refined @BStep@ e
vidence establishes that the final state
@s'' = set "y"   30 s'@ where the intermediate state
@s' = set "x"   20 s@. Thus, refinement typing for @legXY@
proceeds by generating the VC
%
$$ \forall s, s', s''.s' = \vset{x}{20}{s}\ \Rightarrow\ s'' = \vset{y}{30}{s'}\ \Rightarrow\ \vget{x}{s''} \leq \vget{y}{s''}$$
%
which is readily validated by the SMT solver.

\subsection{Floyd-Hoare Logic}\label{sec:deductive:rules}

The above examples show that while
establishing the legitimacy of triples
\emph{explicitly} from the big-step
semantics is possible, it quickly
gets tedious for complex code.
%
The ingenuity of Floyd and Hoare lay
in their design of a recipe to derive
triples based on \emph{symbolically}
transforming the assertions in a
\emph{syntax} directed fashion.

\mypara{Substitutions}
%
The key transformation is a means
to \emph{substitute} all occurrences
of an identifier @x@ with an expression
@e@ in a boolean assertion, as formalized
respectively by @sub@ and @bsub@ in \cref{fig:sub}.

\begin{figure}[t]
\begin{code}
bsub :: Id -> AExp -> BExp -> BExp
bsub x a (Bc  b)     = Bc  b
bsub x a (Not b)     = Not (bsub x a b)
bsub x a (And b1 b2) = And (bsub x a b1) (bsub x a b2)
bsub x a (Leq a1 a2) = Leq (sub  x a a1) (sub  x a a2)
bsub x a (Eql a1 a2) = Eql (sub  x a a1) (sub  x a a2)

sub :: Id -> AExp -> AExp -> AExp
sub x e (Plus  a1 a2)  = Plus  (sub x e a1) (sub x e a2)
sub x e (Minus a1 a2)  = Minus (sub x e a1) (sub x e a2)
sub x e (Times a1 a2)  = Times (sub x e a1) (sub x e a2)
sub x e (V y) | x == y = e
sub _ _ a              = a
\end{code}
\caption{Substituting a variable \texttt{x} with an expression \texttt{e}.}
\label{fig:sub}
\end{figure}

\mypara{Derivation Rules}
%
We write $\fhp{p}{c}{q}$ to say there
exists a tree whose root is the triple
denoted by $p$, $c$ and $q$, using the
syntax-directed rules in \cref{fig:fh}.
%
As with the big-step semantics we can
reify the evidence corresponding to a
Floyd-Hoare derivation via the refined
datatype @FH p c q@ specified
in \cref{fig:fh:code}.
%
Note that the constructors for the datatype
mirror the corresponding derivation rules
in \cref{fig:fh}, and that we have split the
classic rule of \emph{consequence} into separate
rules for strengthening preconditions (\rulename{FH-Pre})
and weakening postconditions (\rulename{FH-Post}).

\begin{figure}[t]
\judgementHead{Floyd-Hoare Logic}{\fhp{p}{c}{q}}
\begin{mathpar}
\inferrule
  { }
  { \fhp{\cSkip}{q}{q} }
  { \rulename{FH-Skip} }

\inferrule
  {  }
  { \fhp{\texttt{bsub}\ x\ e\ q}{\cAsgn{x}{e}}{q} }
  { \rulename{FH-Asgn} }

\inferrule
  {
    \fhp{p}{c_1}{q}  \and
    \fhp{q}{c_2}{r}
  }
  { \fhp{p}{\cSeq{c_1}{c_2}}{r} }
  {\rulename{FH-Seq}}

\inferrule
  {
    \fhp{p \wedge b}{c_1}{q}      \and
    \fhp{p \wedge \neg b}{c_2}{q}
  }
  {
    \fhp{p}{\cIf{b}{c_1}{c_2}}{q}
  }
  {\rulename{FH-If}}

\inferrule
  {
    \fhp{\mathit{inv} \wedge b}{c}{\mathit{inv}}
  }
  {
    \fhp{\mathit{inv}}{\cWhile{b}{c}}{\mathit{inv} \wedge \neg b}
  }
  {\rulename{FH-Whl}}

\inferrule
  {
    \texttt{Valid}(p' \Rightarrow p) \and
    \fhp{p}{c}{q}
  }
  {
    \fhp{p'}{c}{q}
  }
  {\rulename{FH-Pre}}

\inferrule
  {
    \fhp{p}{c}{q} \and
    \texttt{Valid}(q \Rightarrow q')
  }
  {
    \fhp{p}{c}{q'}
  }
  {\rulename{FH-Post}}
\end{mathpar}
\caption{Syntax-driven derivation rules for Floyd-Hoare Logic}
\label{fig:fh}
\end{figure}

\begin{figure}[t]
\begin{code}
{-@ data FH where
     FHSkip :: q:_ ->
               FH q Skip q

     FHAsgn :: q:_ -> x:_ -> a:_ ->
               FH (bsub x a q) (Assign x a) q

     FHSeq  :: p:_ -> c1:_ -> q:_ -> c2:_ -> r:_ ->
               FH p c1 q -> FH q c2 r ->
               FH p (Seq c1 c2) r

     FHIf :: p:_ -> q:_ -> b:_ -> c1:_ -> c2:_ ->
             FH (p .&&. b) c1 q -> FH (p .&&. Not b) c2 q ->
             FH p (If b c1 c2) q

     FHWhl :: inv:_ -> b:_ -> c:_ ->
              FH (inv .&&. b) c inv ->
              FH inv (While inv b c) (inv .&&. Not b)

     FHPre  :: p':_ -> p:_ -> q:_ -> c:_ ->
               Valid (p' .=>. p) -> FH p c q ->
               FH p' c q

     FHPost :: p:_ -> q:_ -> q':_ -> c:_ ->
               FH p c q -> Valid (q .=>. q') ->
               FH p c q'                    @-}
\end{code}
\caption{Reifying Floyd-Hoare Proofs as a Refined Datatype}
\label{fig:fh:code}
\end{figure}

\subsection{Soundness}\label{sec:deductive:sound}

Next, let us verify that the Floyd-Hoare
derivation rules are \emph{sound}, \ie
that $\fhp{p}{c}{q}$ implies $\legit{p}{c}{q}$.
%
To do so, we will prove \emph{legitimacy} lemmas
that verify that if the antecedents of each derivation
rule describe legitimate triples, then the consequent
is also legitimate.

\mypara{Legitimacy for Assignments}
%
For assignments we prove, by induction on the structure of
the assertion @q@, a lemma that connects state-update with
substitution
%
\begin{spec}
lemBsub :: x:_ -> a:_ -> q:_ -> s:_ ->
   {bval (bsub x a q) s = bval q (set x (aval a s) s) }
\end{spec}
%
after which we use the big-step definition to verify
%
\begin{spec}
lemAsgn :: x:_ -> a:_ -> q:_ ->
   Legit (bsub x a q) (Assign x a) q
\end{spec}

\mypara{Legitimacy for Branches and Loops}
%
Similarly, for branches and loops we use the big-step
derivations to respectively prove that
%
\begin{spec}
lemIf :: b:_ -> c1:_ -> c2:_ -> p:_ -> q:_ ->
   Legit (p .&&. b) c1 q -> Legit (p .&&. Not b) c2 q ->
   Legit p (If b c1 c2)  q
\end{spec}
%
The proof (\ie implementation of @lem_if@) proceeds by
splitting cases on the big-step derivation used for
the branch and applying the legitimacy
function for the appropriate branch to
prove the postcondition @q@ holds in
the output.
%
\begin{spec}
lemIf b c1 c2 p q l1 l2 =
  \s s' bs -> case bs of
    BIfT _ _ _ _ _ c1_s_s' ->  -- then branch
      l1 s s' c1_s_s'          -- ... post-cond via l1
    BIfF _ _ _ _ _ c2_s_s' ->  -- else branch
      l2 s s' c2_s_s'          -- ... post-cond via l2
\end{spec}
%
The legitimacy lemma for loops is similar.
%
\begin{spec}
lemWhile :: b:_ -> c:_ -> inv:_ ->
   Legit (inv .&&. b) c inv ->
   Legit inv (While b c) (inv .&&. Not b)
\end{spec}

\mypara{Soundness of Floyd-Hoare Logic}
%
We use the above lemmas to establish
the soundness of Floyd-Hoare logic as:
%
\begin{spec}
thmFHLegit :: p:_ -> c:_ -> q:_ -> FH p c q -> Legit p c q
\end{spec}
%
The implementation of @thm_fh_legit@ is an induction (\ie recursion)
over the \emph{structure} of the evidence @FH p c q@, recursively
invoking the theorem to inductively assume soundness for the
sub-commands, and then using \emph{legitimacy lemmas} that
establish legitimacy for that case via the big-step semantics.

\begin{comment}
\begin{code}
type Legit = State -> State -> BStep -> Proof


{-@ reflect y_x_1 @-}

legXY :: Legit

{-@ reflect x20_y30 @-}
-- | {True}  X <~ 5  {X = 5} ---------------------------------------------------

{-@ leg1 :: Legit tt (Assign {"x"} (N 5)) (V {"x"} .==. N 5) @-}
leg1 :: Legit
leg1 s s' (BAsgn {})
  = ()


-- | {True}  X <~ 5; y <- X  {X = 5} -------------------------------------------

{-@ leg3 :: Legit tt (Seq (Assign {"x"} (N 5)) (Assign {"y"} (V {"x"}))) (Eql (V {"y"}) (N 5)) @-}
leg3 :: Legit
leg3 s s' (BSeq _ _ _ smid _ (BAsgn {}) (BAsgn {}))
  = ()

-- | {False}  X <~ 5  {X = 0} --------------------------------------------------

{-@ leg5 :: Legit ff (Assign {"x"} (N 5)) (Eql (V {"x"}) (N 22)) @-}
leg5 :: Legit
leg5 s s' _ = ()


--------------------------------------------------------------------------------
-- | Two simple facts about Floyd-Hoare Triples --------------------------------
--------------------------------------------------------------------------------

{-@ lem_post_true :: p:_ -> c:_ -> Legit p c tt @-}
lem_post_true :: Assertion -> Com -> Legit
lem_post_true p c = \s s' c_s_s' -> ()

{-@ lem_pre_false :: c:_ -> q:_ -> Legit ff c q @-}
lem_pre_false :: Com -> Assertion -> Legit
lem_pre_false c q = \s s' c_s_s' -> ()


-- forall s. bval P s == True
-- {- type Valid P = s:State -> { v: Proof | bval P s } @-}
type Valid = State -> Proof

-- x >= 0 || x < 0

{-@ checkValid :: p:_ -> Valid p -> () @-}
checkValid :: Assertion -> Valid -> ()
checkValid p v = ()

-- x <= 0
ex0 = checkValid (e0 .=>. e1) (\_ -> ())
  where
    e0 = V "x" .<=. N 0
    e1 = (V "x" .-. N 1) .<=. (N 0)

-- x <= 0 => x - 1 <= 0
-- e1 = e0 `bImp` ((V "x" `Minus` N 1) `Leq` (N 0))

--------------------------------------------------------------------------------
-- | When does an assertion `Imply` another
--------------------------------------------------------------------------------

{-@ type Imply P Q = Valid (P .=>. Q) @-}

-- 10 <= x => 5 <= x
{-@ v1 :: _ -> Imply (Leq (N 10) (V {"x"})) (Leq (N 5) (V {"x"})) @-}
v1 :: a -> Valid
v1 _ = \_ -> ()

-- (0 < x && 0 < y) ===> (0 < x + y)
{-@ v2 :: _ -> Imply (bAnd (Leq (N 0) (V {"x"})) (Leq (N 0) (V {"y"})))
                     (Leq (N 0) (Plus (V {"x"}) (V {"y"})))
  @-}
v2 :: a -> Valid
v2 _ = \_ -> ()

--------------------------------------------------------------------------------
-- | The Floyd-Hoare proof system
--------------------------------------------------------------------------------

{-@ type FH P C Q = {v:_ | prop v = FHProp P C Q} @-}

data FHProp where
  FHProp :: Assertion -> Com -> Assertion -> FHProp

data FH where
  FHSkip :: Assertion -> FH
  FHAsgn :: Assertion -> Id -> AExp -> FH
  FHSeq  :: Assertion -> Com -> Assertion -> Com -> Assertion -> FH -> FH -> FH
  FHIf   :: Assertion -> Assertion -> BExp -> Com -> Com -> FH -> FH -> FH
  FHWhl  :: Assertion -> BExp -> Com -> FH -> FH
  FHPre  :: Assertion -> Assertion -> Assertion -> Com -> Valid -> FH -> FH
  FHPost :: Assertion -> Assertion -> Assertion -> Com -> FH -> Valid -> FH

{-@ lemBsub :: x:_ -> a:_ -> b:_ -> s:_ ->
      { bval (bsub x a b) s = bval b (asgn x a s) }
  @-}
lemBsub :: Id -> AExp -> BExp -> State -> Proof
lemBsub x a (Bc _) _      = ()
lemBsub x a (Not b)     s = lemBsub x a b  s
lemBsub x a (And b1 b2) s = lemBsub x a b1 s &&& lemBsub x a b2 s
lemBsub x a (Leq a1 a2) s = lemSub  x a a1 s &&& lemSub  x a a2 s
lemBsub x a (Eql a1 a2) s = lemSub  x a a1 s &&& lemSub  x a a2 s

{-@ lemSub :: x:_ -> a:_ -> e:_ -> s:_ ->
      { aval (sub x a e) s = aval e (asgn x a s) }
  @-}
lemSub :: Id -> AExp -> AExp -> State -> Proof
lemSub x a (V y) s
  | x == y                    = ()
  | otherwise                 = S.lemma_get_not_set y x (aval a s) s
lemSub x a (N i) s         = ()
lemSub x a (Plus  e1 e2) s = lemSub x a e1 s &&& lemSub x a e2 s
lemSub x a (Minus e1 e2) s = lemSub x a e1 s &&& lemSub x a e2 s
lemSub x a (Times e1 e2) s = lemSub x a e1 s &&& lemSub x a e2 s
\end{code}
\end{comment}
