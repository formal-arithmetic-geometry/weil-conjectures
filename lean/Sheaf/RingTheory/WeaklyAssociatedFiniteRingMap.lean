/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q116
-/
module

public import Mathlib.Algebra.Module.RingHom
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.Maximal

/-!
# Weak association under a finite ring map

Source: Stacks Project, Algebra, Tag 05E1, `lemma-weakly-ass-finite-ring-map`,
the inclusion from the image of the weak assassin over the finite algebra
(blueprint: lem-trf-finite-ring-map-weakass-contraction).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

namespace Module

/-- Weakly associated primes of an arbitrary module contract along a module-finite ring map.
Source: Stacks Project, Algebra, Tag 05E1, `lemma-weakly-ass-finite-ring-map`,
the contraction inclusion (blueprint: lem-trf-finite-ring-map-weakass-contraction).

The finite-generation condition uses the R-action on S induced by the given ring map.
The conclusion uses exactly the restricted R-action `r • x = φ r • x` on P, supplied by
`Module.compHom P φ`, rather than an independently chosen module structure.
Weak association is expressed as existence of an element whose annihilator colon ideal
has the given prime as a minimal prime. No Noetherian or finite-generation condition on P
is imposed.

Proof:
1. Choose $m\in P$ such that $\mathfrak q$ is minimal over $J=\operatorname{Ann}_S(m)$, and put
$\mathfrak p=\varphi^{-1}(\mathfrak q)$. Then $J\subseteq\mathfrak q$. By
[lem-weil-pbc-minimal-prime-localization-radical], $\sqrt{JS_{\mathfrak q}}=\mathfrak
qS_{\mathfrak q}$. Also $m/1\ne0$ in $P_{\mathfrak q}$: otherwise the zero criterion of
[def-weil-pbc-module-localization] gives $v\notin\mathfrak q$ with $vm=0$, contradicting
$J\subseteq\mathfrak q$.

2. By [lem-weil-pbc-spec-finite-ring-map-finite], the map $f=\operatorname{Spec}(\varphi)$ is
finite. Its fibre over $\mathfrak p$ is finite by clause (2) of
[lem-weil-pbc-finite-closed-map-finite-fibres]. The spectrum convention
[def-weil-affine-spectrum] identifies this fibre with the primes of $S$ whose contraction is
$\mathfrak p$. Enumerate them without repetition as $\mathfrak q_1=\mathfrak q,\mathfrak
q_2,\ldots,\mathfrak q_l$, with $l\ge1$. The map $R\to S$ is integral by
[lem-weil-pbc-finite-algebra-is-integral]. Hence [pqf-lem-incomparability] shows that these
distinct primes are pairwise incomparable.

3. If $l>1$, apply [lem-weil-pbc-prime-avoidance] with the ideal $\mathfrak q$ and the prime
ideals $\mathfrak q_2,\ldots,\mathfrak q_l$. The noncontainment hypotheses follow from step 2.
Obtain $x\in\mathfrak q$ with $x\notin\mathfrak q_i$ for every $i>1$. If $l=1$, take $x=0$; the
avoidance condition is empty.

4. Step 1 gives $(x/1)^t\in JS_{\mathfrak q}$ for some $t\ge1$. Thus $x^tm/1=0$ in $P_{\mathfrak
q}$, and [def-weil-pbc-module-localization] gives $y\notin\mathfrak q$ with $yx^tm=0$ in $P$.
Put $z=ym$. Since $y$ is invertible in $S_{\mathfrak q}$ and $m/1\ne0$, we have $z/1\ne0$ in
$P_{\mathfrak q}$. For $i>1$, $x$ is invertible in $S_{\mathfrak q_i}$ and $x^tz=0$, so $z/1=0$
in $P_{\mathfrak q_i}$.

5. Put $T=R\setminus\mathfrak p$, $A=T^{-1}R=R_{\mathfrak p}$, $B=\varphi(T)^{-1}S$ and
$N=\varphi(T)^{-1}P$. These fractions and their actions are those of
[def-weil-pbc-module-localization]. The map $A\to B$ is $r/t\mapsto\varphi(r)/\varphi(t)$, well
defined by the fraction relations. If $s_1,\ldots,s_d$ generate $S$ over $R$, they generate $B$
over $A$: $s/\varphi(t)=\sum_j(a_j/t)(s_j/1)$ whenever $s=\sum_j\varphi(a_j)s_j$. Thus $B$ is
finite over the local ring $A$, whose maximal ideal is $\mathfrak pA$ by
[def-weil-pbc-localization-at-prime]. For every maximal ideal $\mathfrak n$ of $B$,
[lem-weil-pbc-finite-algebra-local-radical] gives its contraction $\mathfrak pA$ in $A$. By
[lem-weil-pbc-localization-spectrum-embedding], its contraction $Q$ in $S$ is prime. For $r\in
R$, $\varphi(r)\in Q$ iff $r/1\in\mathfrak pA$ iff $r\in\mathfrak p$ (the last equivalence is
the fraction criterion and primality of $\mathfrak p$). Consequently $Q=\mathfrak q_i$ for some
$i$.

6. Fix $r\in\mathfrak p$. By step 1, $(\varphi(r)/1)^k\in JS_{\mathfrak q}$ for some $k\ge1$.
Hence $\varphi(r)^kz/1=0$ in $P_{\mathfrak q}$; by step 4 it is also zero in every $P_{\mathfrak
q_i}$ for $i>1$. Let $w=\varphi(r)^kz/1\in N$. If $w\ne0$, its annihilator
$H=\operatorname{Ann}_B(w)$ is proper. Choose a maximal ideal $\mathfrak n\supseteq H$ by
[lem-weil-pbc-proper-ideal-contained-in-maximal]. Step 5 identifies its contraction in $S$ with
some $\mathfrak q_i$. Since $\varphi(r)^kz/1=0$ in $P_{\mathfrak q_i}$,
[def-weil-pbc-module-localization] gives $u\notin\mathfrak q_i$ with $u\varphi(r)^kz=0$ in $P$.
Then $u/1\in H\subseteq\mathfrak n$, contradicting the description of the contraction. Thus
$w=0$ in $N$, and the same zero criterion yields $a\in R\setminus\mathfrak p$ with
$\varphi(a)\varphi(r)^kz=0$. In other words, $ar^k\in\operatorname{Ann}_R(z)$.

7. Write $I=\operatorname{Ann}_R(z)$. If $b\in I\setminus\mathfrak p$, then
$\varphi(b)\notin\mathfrak q$ is invertible in $S_{\mathfrak q}$ and kills $z/1$, contradicting
step 4; hence $I\subseteq\mathfrak p$. Let $\mathfrak p_0\subseteq\mathfrak p$ be a prime
containing $I$. For each $r\in\mathfrak p$, step 6 gives $a\notin\mathfrak p$ and $k\ge1$ with
$ar^k\in I\subseteq\mathfrak p_0$. As $a\notin\mathfrak p_0$, primality implies $r\in\mathfrak
p_0$. Thus $\mathfrak p\subseteq\mathfrak p_0$, and equality follows. This proves that
$\mathfrak p$ is minimal over the annihilator of the actual element $z\in P$, which is exactly
$\mathfrak p\in\operatorname{WeakAss}_R(P)$. -/
theorem weakly_associated_comap_of_finite
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] (φ : R →+* S)
    (hfinite : @Module.Finite R S _ _ (Module.compHom S φ))
    (P : Type w) [AddCommGroup P] [Module S P] (q : Ideal S)
    (hq : ∃ x : P, q ∈ ((⊥ : Submodule S P).colon {x}).minimalPrimes) :
    ∃ x : P, q.comap φ ∈
      (@Submodule.colon R P _ _ (Module.compHom P φ) ⊥ {x}).minimalPrimes := by
  sorry

end Module
