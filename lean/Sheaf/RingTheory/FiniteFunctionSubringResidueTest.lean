/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Authors: SHEAF contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.Algebra.CharP.Defs

import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# Proper ideals in finite function subrings admit residue evaluation tests

Source: literature/stacks-project/algebra.tex, agent-written finite-product consequence
of Tags 00GQ, 00GR and 00GS (blueprint: lem-per-finite-function-subring-residue-test).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Subring

/-- Every proper ideal in a finite function subring has a coordinate residue test, and the
corresponding residue field is finite of prime characteristic.

Source: literature/stacks-project/algebra.tex, agent-written finite-product consequence of
Tags 00GQ, 00GR and 00GS (blueprint: lem-per-finite-function-subring-residue-test).

Proof (to be formalised in stage 3), following the six steps of the DAG:

1. Put $C=A^X$ and let $j:B\hookrightarrow C$ be inclusion. Write $c_a\in B$ for the constant
   function with value $a\in A$. For $g\in C$, form $P_g(T)=\prod_{x\in X}(T-c_{g(x)})\in B[T]$. Its
   leading coefficient is the product of the leading coefficients $1$, so it is monic. At every
   coordinate $y\in X$, evaluation at $g$ gives $P_g(g)(y)=\prod_{x\in X}(g(y)-g(x))=0$, because the
   factor indexed by $y$ is zero. Thus $P_g(g)=0$ in $C$. This proves directly that every element of
   $C$ is integral over $B$, meaning a root of a monic polynomial over $B$. The inclusion $j$ is
   injective.

2. Apply [lem-weil-pbc-proper-ideal-contained-in-maximal] to $I\subsetneq B$ to choose a maximal
   ideal $M\supseteq I$. It is prime: if $ab\in M$ and $a\notin M$, maximality gives $1=u+ra$ with
   $u\in M$, $r\in B$, hence $b=ub+rab\in M$. Apply [lem-weil-pbc-integral-injective-lying-over] to
   the integral injective inclusion $j$ established in Step 1 and the prime $M$. It supplies a prime
   ideal $P\subset C$ with $j^{-1}(P)=M$.

3. By [lem-weil-pbc-integral-prime-over-maximal-maximal], the prime $P$ is maximal, since $C$ is
   integral over $B$ and $j^{-1}(P)=M$ is maximal. Apply [lem-weil-pbc-product-prime-factor] to the
   finite product $C=\prod_{x\in X}A$. There are $x\in X$ and a prime $\mathfrak q\subset A$ with
   $P=\operatorname{ev}_x^{-1}(\mathfrak q)$. This $\mathfrak q$ is maximal: if $\mathfrak
   q\subseteq J\subsetneq A$ is an ideal, then $\operatorname{ev}_x^{-1}(J)$ is a proper ideal
   containing $P$, hence equals $P$. Evaluation is surjective, since $\operatorname{ev}_x(c_a)=a$,
   so taking images yields $J=\mathfrak q$. For every $f\in I\subseteq M=j^{-1}(P)$ we now have
   $f(x)\in\mathfrak q$, proving the evaluation assertion.

4. By [lem-weil-common-extension-fields-quotient-field], $K=A/\mathfrak q$ is a field. It is nonzero
   since $\mathfrak q$ is proper, so $1+\mathfrak q\ne0+\mathfrak q$. Choose additive generators
   $a_1,\ldots,a_r$ of $A$ as in [def-weil-finitely-generated-module]. The quotient map of
   [def-weil-pbc-quotient-module] is surjective and additive. Consequently every element of $K$ has
   the form $\sum_{t=1}^r n_t(a_t+\mathfrak q)$ with $n_t\in\mathbf Z$, and the additive group of
   $K$ is finitely generated.

5. Apply [lem-sbc-finitely-generated-abelian-group-structure] to the additive group of $K$. It gives
   $K\simeq\mathbf Z^n\times T$ additively, where $T$ is a direct sum indexed by a finite set of
   groups $\mathbf Z/(p_i^{e_i})$, with $p_i$ prime and $e_i\geq0$. If $n>0$, a free-coordinate
   projection composed with this isomorphism gives a surjective additive map $h:K\to\mathbf Z$. When
   $2\cdot1_K=0$, every $z\in K$ satisfies $2z=(2\cdot1_K)z=0$; choosing $h(z)=1$ would give
   $0=h(2z)=2$, a contradiction in $\mathbf Z$. When $2\cdot1_K\ne0$, multiplication by $2\cdot1_K$
   is surjective, since it has a multiplicative inverse in $K$. Choose $z$ with $h(z)=1$ and $w$
   with $2w=z$; then $1=2h(w)$, again impossible in $\mathbf Z$. Thus $n=0$. Each $p_i^{e_i}$ is
   positive, including the case $e_i=0$, and each cyclic group has that finite number of residue
   classes. An element of $T$ is a tuple in the product of these finitely many finite sets, so $T$,
   and hence $K$, is finite.

6. Since $K$ is finite, two members of the infinite list $0,1_K,2\cdot1_K,\ldots$ agree. Their
   difference gives a positive integer annihilating $1_K$. Let $p$ be the least such integer; it is
   not $1$, because $K$ is nonzero. If $p=uv$ with $1<u,v<p$, minimality says $u\cdot1_K$ and
   $v\cdot1_K$ are nonzero, whereas their product is $p\cdot1_K=0$. This contradicts the absence of
   zero divisors in a field. Thus $p$ is prime and is the characteristic of $K$, as required.
-/
theorem exists_maximal_residue_of_ne_top
    {A : Type u} [CommRing A] [Nontrivial A] [Module.Finite ℤ A]
    {X : Type v} [Finite X] [Nonempty X]
    (B : Subring (X → A))
    (hconst : ∀ a : A, (fun _ : X ↦ a) ∈ B)
    (I : Ideal B) (hI : I ≠ ⊤) :
    ∃ (x : X) (q : Ideal A), q.IsMaximal ∧
      (∀ f : B, f ∈ I → (f : X → A) x ∈ q) ∧
      IsField (A ⧸ q) ∧ Finite (A ⧸ q) ∧
      Nontrivial (A ⧸ q) ∧
      ∃ p : ℕ, Nat.Prime p ∧ CharP (A ⧸ q) p := by
  sorry

end Subring
