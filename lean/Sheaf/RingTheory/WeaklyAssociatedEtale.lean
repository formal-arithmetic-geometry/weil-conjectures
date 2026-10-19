/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.AdjoinRoot
import Sheaf.RingTheory.WeakAssLocalization

/-!
# Weak association under etale base change

Source: Stacks Project, More on Flatness, Tag 05FP,
`lemma-etale-weak-assassin-up-down`, in its affine module formulation
(blueprint: lem-trf-etale-weakass-invariance).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

open scoped TensorProduct

namespace Module

/-- Weak association of an arbitrary module is preserved and reflected at each prime of an
etale algebra. Source: Stacks Project, More on Flatness, Tag 05FP,
`lemma-etale-weak-assassin-up-down`, in affine form
(blueprint: lem-trf-etale-weakass-invariance).

`Algebra.Etale A B` is the affine etaleness of the spectrum map in
[def-weil-etale-morphism], by `HasRingHomProperty.Spec_iff` and
`RingHom.etale_algebraMap`. An algebra structure records the given ring homomorphism.
The annihilator of an element is `(⊥ : Submodule _ _).colon {x}`, and weak association is
membership in its `Ideal.minimalPrimes`, with no Noetherian hypothesis.
The witness `z` lies in `L ⊗[A] B`. Its annihilator is computed after the tensor swap into
`B ⊗[A] L`, whose usual first-factor B-action is exactly the second-factor action on `z`.

Proof (the seven steps of the DAG node):

1. For ascent, assume $\mathfrak a\in\operatorname{WeakAss}_A(L)$. Put $R=A_{\mathfrak a}$,
$S=B_{\mathfrak b}$, $M=L_{\mathfrak a}$ and $N=L\otimes_A B$. By [lem-sc-weakass-localization],
there is $x\in M$ with $\sqrt{I}=\mathfrak aR$, where $I=\operatorname{Ann}_R(x)$. The etale
hypothesis [def-weil-etale-morphism] gives flatness of the spectrum morphism;
[lem-weil-pbc-flat-ring-map-iff-flat-affine] gives flatness of $A\to B$, and
[lem-weil-pbc-flat-local-ring-maps] gives flatness of the induced local map $R\to S$. All these
statements allow arbitrary rings; neither $L$ nor its localization is assumed finite.

2. The map $R/I\to M$, $[r]\mapsto rx$, is injective by the definition of $I$. Flatness
[def-weil-pbc-flat-ring-map] therefore makes $(R/I)\otimes_R S\to M\otimes_R S$ injective. The
tensor definition identifies its source with $S/IS$: $[r]\otimes s\mapsto[rs]$, with inverse
$[s]\mapsto[1]\otimes s$. The relations on both sides verify these maps are well defined and
inverse. If $y=x\otimes1$, injectivity gives $\operatorname{Ann}_S(y)=IS$. Also $M\otimes_R S\cong
N_{\mathfrak b}$: the map $(l/u)\otimes(b/v)\mapsto(l\otimes b)/(\varphi(u)v)$ has inverse
$(l\otimes b)/v\mapsto(l/1)\otimes(b/v)$, extended additively. The fraction relations and tensor
balancing verify the two inverse formulas. Here $u\notin\mathfrak a$, $v\notin\mathfrak b$, so
every displayed denominator is invertible.

3. By [lem-weil-pbc-etale-prime-generates-maximal], $(\mathfrak aR)S=\mathfrak bS$. Thus
$IS\subseteq\mathfrak bS$. For $z\in\mathfrak bS$, write $z=\sum_{i=1}^k s_i a_i$ with
$a_i\in\mathfrak aR$. Since $\sqrt I=\mathfrak aR$, choose $e_i\ge1$ with $a_i^{e_i}\in I$. Every
term in the expansion of $z^{1+\sum_i(e_i-1)}$ contains some $a_i^{e_i}$, so this power lies in
$IS$ (and $z=0$ is immediate). Hence $\sqrt{IS}=\mathfrak bS$. The element $y$ of step 2 is
therefore a radical-annihilator witness in $N_{\mathfrak b}$, and [lem-sc-weakass-localization]
gives $\mathfrak b\in\operatorname{WeakAss}_B(N)$. This proves ascent without a finite-generation
assumption.

4. For descent, assume $\mathfrak b\in\operatorname{WeakAss}_B(N)$. Apply
[lem-weil-pbc-etale-locally-standard] to choose $g\notin\mathfrak b$ and an $A$-algebra
isomorphism $B_g\cong C_h$, where $C=A[t]/(f)$ and $f$ is monic. Let $\mathfrak b_g$ be the prime
in $B_g$ consisting of fractions whose numerator lies in $\mathfrak b$. This is well defined and
prime because $g\notin\mathfrak b$; its inverse image in $B$ is $\mathfrak b$. Transport it to a
prime of $C_h$ and contract to $\mathfrak r\subset C$. Then $h\notin\mathfrak r$, its extension is
the transported prime (a fraction belongs exactly when its numerator does), and $\mathfrak r\cap
A=\mathfrak a$. By [lem-weil-pbc-monic-quotient-free], $C$ is a finite free $A$-module with power
basis $e_1,\ldots,e_n$. The existence of $\mathfrak r$ rules out $n=0$, for the monic degree-zero
polynomial is $1$ and its quotient is the zero ring.

5. Put $K=L\otimes_A C$. Localization at the displayed primes gives $B_{\mathfrak
b}\cong(B_g)_{\mathfrak b_g}\cong(C_h)_{\mathfrak rC_h}\cong C_{\mathfrak r}$. These
identifications follow directly from fractions: if $s$ is outside a prime, inverting $s$ and then
all elements outside the extended prime is the same as inverting all elements outside the original
prime, with $(a/s^i)/(b/s^j)\mapsto as^j/(bs^i)$. Tensoring with $L$ has the analogous explicit
identification $(l\otimes c)/v\leftrightarrow l\otimes(c/v)$; its inverse and balancing follow
from the same fraction relation. Thus $N_{\mathfrak b}\cong K_{\mathfrak r}$, compatibly with the
local ring isomorphism and their maximal ideals. By [lem-sc-weakass-localization] applied first to
$(B,N,\mathfrak b)$ and then to $(C,K,\mathfrak r)$, the assumed weak association at $\mathfrak b$
gives weak association at $\mathfrak r$: the radical-annihilator witness in the first localized
module maps to one in the second, and the converse localization criterion returns $\mathfrak
r\in\operatorname{WeakAss}_C(K)$.

6. The map $A\to C$ is finite by step 4. Apply [lem-trf-finite-ring-map-weakass-contraction] to
the arbitrary $C$-module $K$ and its weakly associated prime $\mathfrak r$. Its contraction is
$\mathfrak a$, so $\mathfrak a\in\operatorname{WeakAss}_A(K)$, where $K$ now denotes the module
with its restricted $A$-action. This step uses finiteness of $C$ over $A$, not finiteness of $K$
over either ring.

7. The basis from step 4 identifies $K$ with $L^n$: $l\otimes\sum_i a_i e_i\mapsto(a_i l)_i$, with
inverse $(l_i)_i\mapsto\sum_i l_i\otimes e_i$. The tensor relations verify these are inverse
$A$-linear maps. Choose a witness $(l_1,\ldots,l_n)$ for step 6, and set
$I_i=\operatorname{Ann}_A(l_i)$. Its annihilator is $J=\bigcap_i I_i$, and $\mathfrak a$ is
minimal over $J$. Since $\prod_i I_i\subseteq J\subseteq\mathfrak a$ and $\mathfrak a$ is prime,
some $I_j\subseteq\mathfrak a$: otherwise choose $a_i\in I_i\setminus\mathfrak a$ and their
product contradicts primality. Any prime $\mathfrak p$ with $I_j\subseteq\mathfrak
p\subseteq\mathfrak a$ contains $J$, so minimality over $J$ forces $\mathfrak p=\mathfrak a$. Thus
$\mathfrak a$ is minimal over $\operatorname{Ann}_A(l_j)$, proving $\mathfrak
a\in\operatorname{WeakAss}_A(L)$. Together with step 3 this proves both directions.
-/
theorem weakly_associated_tensor_iff_of_etale
    (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B]
    [Algebra.Etale A B] (L : Type w) [AddCommGroup L] [Module A L]
    (b : Ideal B) [b.IsPrime] :
    (∃ z : L ⊗[A] B,
      b ∈ ((⊥ : Submodule B (B ⊗[A] L)).colon
        {TensorProduct.comm A L B z}).minimalPrimes) ↔
      ∃ x : L,
        b.comap (algebraMap A B) ∈ ((⊥ : Submodule A L).colon {x}).minimalPrimes := by
  sorry

end Module
