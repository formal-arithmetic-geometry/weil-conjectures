/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q148
-/
module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes
import Sheaf.RingTheory.WeakAssLocalization
import Sheaf.RingTheory.AnnihilatorEqIffMinimalPrimeOfFG
import Sheaf.RingTheory.LocalUniversalInjectiveResidue
import Sheaf.RingTheory.ProjectiveOverLocalFree
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Weak association after flat finitely presented base change

Source: Stacks Project, More on Flatness, Tag 05IG, lemma-weak-bourbaki-pre, specialized to N = S
(blueprint: lem-trf-flat-tensor-weakass-fibre).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

open scoped TensorProduct

namespace Module

/-- Weak association after flat finitely presented algebra base change is equivalent to
weak association on the base and exact-annihilator association in the fibre.

Source: Stacks Project, More on Flatness, Tag 05IG, lemma-weak-bourbaki-pre, with N = S
(blueprint: lem-trf-flat-tensor-weakass-fibre).

The witness `z` belongs to `M ⊗[R] S`. Its S-annihilator for the second-factor action is
written as the annihilator of `TensorProduct.comm R M S z` in `S ⊗[R] M`: the canonical
swap intertwines `s • (m ⊗ t) = m ⊗ (s * t)` with the usual first-factor action.
The fibre is Mathlib's `p.asIdeal.Fiber S = κ(p) ⊗[R] S`, canonically the tensor swap of
the source's fibre. Its prime is the image of q under the recorded fibre-prime bijection.
No Noetherian or module-finiteness assumption is made.

Proof (the thirteen steps of the DAG node):
1. We first record the localization bookkeeping used below. If $U$ is a multiplicative set in a
ring $T$ and $\mathfrak t\cap U=\varnothing$, then $(U^{-1}T)_{U^{-1}\mathfrak t}=T_{\mathfrak t}$
and $(U^{-1}P)_{U^{-1}\mathfrak t}=P_{\mathfrak t}$: the inverse maps on fractions send
$(a/u)/(b/v)$ to $av/(ub)$ and conversely. Thus the local radical-annihilator criterion
[lem-sc-weakass-localization] gives $\mathfrak t\in\operatorname{WeakAss}_T(P)$ iff
$U^{-1}\mathfrak t\in\operatorname{WeakAss}_{U^{-1}T}(U^{-1}P)$. We use this both for principal
localization in $S$ and for localizing the base at $\mathfrak p$. The fibre $C$ is a finite-type
algebra over the field $\kappa(\mathfrak p)$: substitute the images of coefficients in a finite
presentation of $S$. A field is Noetherian since its only ideals are $0$ and the whole field, so
[lem-weil-pbc-finite-type-algebra-noetherian] makes $C$ Noetherian. Every prime of $C$ is
therefore finitely generated, and [lem-sc-ass-weakass-fg-prime] identifies its weakly associated
primes with its exact-annihilator associated primes. The same observations apply to every fibre
ring below.

2. Write $Q=\overline{\mathfrak q}$. The set $E=\operatorname{Ass}_C(C)$ is finite by
[lem-weil-pbc-noetherian-associated-primes-finite]. For each $\mathfrak r\in E$ not contained in
$Q$ choose $a_{\mathfrak r}\in\mathfrak r\setminus Q$ and multiply these elements. The product $a$
lies in every such $\mathfrak r$ and is outside $Q$; an empty product is $1$. Write $a=b/s$ in
$C=S_{\mathfrak p}/\mathfrak pS_{\mathfrak p}$ with $b\in S$, $s\in R\setminus\mathfrak p$, and
put $g=b$. Multiplication by the unit $s$ preserves membership in each prime, so $g\notin\mathfrak
q$ and its image belongs to all the unwanted primes. Replace $S$ by $S_g$ and $\mathfrak q$ by
$\mathfrak qS_g$. Step 1 preserves both the assertion about $\mathfrak q$ and the fibre-associated
assertion. In this new fibre every associated prime contracts to an associated prime of the old
fibre contained in $Q$. The new algebra is still finitely presented (adjoin $t$ with $gt=1$) and
flat: localize the injection obtained by tensoring with the original flat $S$, using
[lem-weil-pbc-localization-module-exact]. We retain $R,S,\mathfrak p,\mathfrak q,C,Q$ for these
localized data.

3. Apply [lem-trf-flat-algebra-etale-projective-neighborhood] to obtain the pointed etale square
$R\to R^{\prime}$, $S\to S^{\prime}$ with primes $\mathfrak p^{\prime},\mathfrak q^{\prime}$ and
projective $R^{\prime}$-module $S^{\prime}$. Put $M^{\prime}=M\otimes_R R^{\prime}$, $W=M\otimes_R
S$, $W^{\prime}=M^{\prime}\otimes_{R^{\prime}}S^{\prime}=W\otimes_S S^{\prime}$,
$C^{\prime}=S^{\prime}\otimes_{R^{\prime}}\kappa(\mathfrak p^{\prime})$, and
$Q^{\prime}=\overline{\mathfrak q^{\prime}}$. The displayed identification sends $(m\otimes
r^{\prime})\otimes s^{\prime}$ to $m\otimes r^{\prime}s^{\prime}$, with inverse $m\otimes
s^{\prime}\mapsto(m\otimes1)\otimes s^{\prime}$. By [lem-trf-etale-weakass-invariance], weak
association of $\mathfrak q$ to $W$ is equivalent to that of $\mathfrak q^{\prime}$ to
$W^{\prime}$, and weak association of $\mathfrak p$ to $M$ is equivalent to that of $\mathfrak
p^{\prime}$ to $M^{\prime}$. Apply the same theorem to the etale map $C\to C^{\prime}$ and then
the Noetherian conversion of Step 1: $Q\in\operatorname{Ass}_C(C)$ iff
$Q^{\prime}\in\operatorname{Ass}_{C^{\prime}}(C^{\prime})$.

4. Every $\mathfrak r^{\prime}\in\operatorname{Ass}_{C^{\prime}}(C^{\prime})$ contracts, by the
etale weak-assassin theorem and Step 1, to an associated prime $\mathfrak r$ of $C$. The choice of
$g$ ensures $\mathfrak r\subseteq Q$. Also there are no strict inclusions between primes of
$C^{\prime}$ with the same contraction to $C$: if $\mathfrak a^{\prime}\subseteq\mathfrak
b^{\prime}$ both contract to $\mathfrak a$, then [lem-weil-pbc-etale-prime-generates-maximal] says
$\mathfrak a C^{\prime}_{\mathfrak b^{\prime}}=\mathfrak b^{\prime}C^{\prime}_{\mathfrak
b^{\prime}}$, and the intermediate prime $\mathfrak a^{\prime}C^{\prime}_{\mathfrak b^{\prime}}$
must equal it; contraction back gives equality. Consequently, whenever $Q^{\prime}$ is associated,
it is maximal among the associated primes of $C^{\prime}$: any associated prime containing it
contracts to a prime both containing and contained in $Q$, and hence equals it.

5. For the first implication suppose initially that $Q$ is not associated. Then $Q^{\prime}$ is
not associated by Step 3. No associated prime $\mathfrak r^{\prime}$ of $C^{\prime}$ can contain
$Q^{\prime}$: contraction and Step 4 would force equality. Apply finite prime avoidance
[lem-weil-pbc-prime-avoidance] to $Q^{\prime}$ and the finite set of associated primes
[lem-weil-pbc-noetherian-associated-primes-finite]. We obtain $a\in Q^{\prime}$ outside their
union, hence multiplication by $a$ on $C^{\prime}$ is injective by
[lem-weil-pbc-noetherian-module-zerodivisors-union-associated-primes]. If that finite set is
empty, take $a=0$ and use the same zero-divisor statement. Since $C^{\prime}=S^{\prime}_{\mathfrak
p^{\prime}}/\mathfrak p^{\prime}S^{\prime}_{\mathfrak p^{\prime}}$, multiply $a$ by a nonzero
residue-field scalar to obtain the image of an $a^{\prime}\in\mathfrak q^{\prime}$; this does not
change injectivity. The lift lies in $\mathfrak q^{\prime}$ because $Q^{\prime}$ contracts to it.

6. Put $A=R^{\prime}_{\mathfrak p^{\prime}}$ and $B=S^{\prime}_{\mathfrak p^{\prime}}$. The module
$B$ is projective over $A$: localize the splitting of $S^{\prime}$ as a summand of a free
$R^{\prime}$-module, obtaining a splitting into a free $A$-module. A free module is flat because
tensoring with it is a direct sum of copies of the input map; its direct summands are flat by
restricting that injection to the summand. Apply [lem-trf-local-universal-injective-residue] to
multiplication by $a^{\prime}$ on $B$; its residue-field map is multiplication by $a$ on
$C^{\prime}$. It is universally injective over $A$, hence injective on $M^{\prime}_{\mathfrak
p^{\prime}}\otimes_A B$ and, after exact localization, on $W^{\prime}_{\mathfrak q^{\prime}}$.
This prevents weak association at $\mathfrak q^{\prime}$: an element with annihilator radical the
maximal ideal would be killed by a power of $a^{\prime}$, and injectivity would force it to be
zero. The local criterion and Step 3 give $\mathfrak q\notin\operatorname{WeakAss}_S(W)$. Thus for
every $M$, weak association at $\mathfrak q$ implies fibre association at $Q$.

7. Now assume $\mathfrak q\in\operatorname{WeakAss}_S(W)$, and choose $z\in W$ with $\mathfrak q$
minimal over $\operatorname{Ann}_S(z)$. Its image in $W_{\mathfrak q}$ is nonzero (otherwise some
element outside $\mathfrak q$ annihilates $z$). For each $f\in\mathfrak p$ there are
$g_f\notin\mathfrak q$ and $n_f\geq1$ with $g_f f^{n_f}z=0$, for this particular $z$: an element
$c/t$ of $S_{\mathfrak q}$ kills $z/1$ iff $ucz=0$ for some $u\notin\mathfrak q$
[def-weil-pbc-module-localization], so $\operatorname{Ann}_{S_{\mathfrak
q}}(z/1)=\operatorname{Ann}_S(z)S_{\mathfrak q}$; a prime of $S_{\mathfrak q}$ containing it is
$\mathfrak tS_{\mathfrak q}$ for a prime $\mathfrak t\subseteq\mathfrak q$ containing
$\operatorname{Ann}_S(z)$, hence $\mathfrak t=\mathfrak q$ by minimality. By
[lem-weil-pbc-zero-locus-eq-iff-radical-eq] the radical of $\operatorname{Ann}_{S_{\mathfrak
q}}(z/1)$ is therefore $\mathfrak qS_{\mathfrak q}$, which contains $f/1$ since $\mathfrak
p\subseteq\mathfrak q$; so $f^{n_f}/1=c/t$ with $c\in\operatorname{Ann}_S(z)$, $t\notin\mathfrak
q$, and clearing denominators gives $g_f\notin\mathfrak q$ with $g_ff^{n_f}z=0$. Let $z^{\prime}$
be the image in $W^{\prime}_{\mathfrak p^{\prime}}$. It is nonzero: the local map $S_{\mathfrak
q}\to S^{\prime}_{\mathfrak q^{\prime}}$ is flat by etaleness [def-weil-etale-morphism,
def-weil-flat-morphism], and faithfully flat by
[lem-pc-local-flat-faithful-flat-reflects-surjective]. A faithfully flat extension preserves
nonzero elements under $x\mapsto x\otimes1$: flatness embeds the tensor of the cyclic submodule
generated by $x$ into the ambient tensor, and if its generator became zero that cyclic tensor
would be zero, whence the cyclic submodule would be zero by faithful flatness
[def-weil-pbc-faithfully-flat-ring-map]. Hence $z$ stays nonzero at $\mathfrak q^{\prime}$, so
already $z^{\prime}\ne0$.

8. The image of $g_f$ in $C^{\prime}$ avoids every associated prime: its contraction in $C$ is
contained in $Q$ by Step 4, whereas $g_f\notin\mathfrak q$. The zero-divisor theorem makes
multiplication by this image injective on $C^{\prime}$. As in Step 6,
[lem-trf-local-universal-injective-residue] makes multiplication by $g_f$ universally injective on
$S^{\prime}_{\mathfrak p^{\prime}}$ over $R^{\prime}_{\mathfrak p^{\prime}}$. Cancelling it in
$g_f f^{n_f}z^{\prime}=0$ gives $f^{n_f}z^{\prime}=0$ for every $f\in\mathfrak p$. Since
$\mathfrak p^{\prime}R^{\prime}_{\mathfrak p^{\prime}}=\mathfrak pR^{\prime}_{\mathfrak
p^{\prime}}$ by [lem-weil-pbc-etale-prime-generates-maximal], the radical of the
$R^{\prime}_{\mathfrak p^{\prime}}$-annihilator of $z^{\prime}$ is its maximal ideal: it contains
the generators from $\mathfrak p$, and is proper because $z^{\prime}\ne0$.

9. The projective module $S^{\prime}_{\mathfrak p^{\prime}}$ is free over the local ring
$R^{\prime}_{\mathfrak p^{\prime}}$ by [lem-trf-projective-over-local-free]. Expanding
$z^{\prime}$ in this basis expresses it as a finite tuple of elements of $M^{\prime}_{\mathfrak
p^{\prime}}$, at least one coordinate $v$ nonzero. Every base element whose power annihilates
$z^{\prime}$ has that same power annihilating $v$; Step 8 therefore makes the radical of
$\operatorname{Ann}(v)$ the maximal ideal. By [lem-sc-weakass-localization] this gives $\mathfrak
p^{\prime}\in\operatorname{WeakAss}_{R^{\prime}}(M^{\prime})$, and by
[lem-trf-etale-weakass-invariance] it gives $\mathfrak p\in\operatorname{WeakAss}_R(M)$. Steps
1--9 have now proved the entire forward implication for every flat finitely presented algebra and
every module, without using the reverse implication.

10. For the reverse implication assume $\mathfrak p\in\operatorname{WeakAss}_R(M)$ and
$Q\in\operatorname{Ass}_C(C)$. Perform Steps 2--4. They preserve these assumptions, make
$S^{\prime}$ projective over $R^{\prime}$, and make $Q^{\prime}$ maximal among the associated
primes of $C^{\prime}$. Localize the base at $\mathfrak p^{\prime}$ and rename the data
$(A,\mathfrak m)$, $B$, $L$, $\mathfrak b$, $D=B/\mathfrak mB$, and $\overline{\mathfrak b}$. Thus
$A$ is local, $B$ is a projective $A$-module and a finitely presented $A$-algebra, $\mathfrak
m\in\operatorname{WeakAss}_A(L)$, and $\overline{\mathfrak b}$ is maximal in
$\operatorname{Ass}_D(D)$. These are the same fibres because tensoring a localized presentation
with the residue field does not change it; projectivity follows by localizing its splitting. Step
1 preserves the relevant weak association. It suffices to prove $\mathfrak
b\in\operatorname{WeakAss}_B(L\otimes_A B)$, since Step 1 and the etale equivalence of Step 3 then
return to the original rings.

11. The local criterion [lem-sc-weakass-localization] gives $y\in L$ such that
$I=\operatorname{Ann}_A(y)$ has radical $\mathfrak m$. The map $A/I\to L$, $\bar a\mapsto ay$, is
injective. Tensoring it with $B$ embeds $B/IB$ into $L\otimes_A B$, since a projective module is a
summand of a free module and tensoring such a summand preserves injections, as explained in Step
6. The same splitting, tensored with $A/I$, shows $B/IB$ is projective over $A/I$. The fibre $D$
is Noetherian by Step 1, so write $\overline{\mathfrak b}=(\bar h_1,\ldots,\bar h_n)$ and lift the
generators to $h_i\in B$; then $\mathfrak b=\mathfrak mB+(h_1,\ldots,h_n)$. These are quotient
lifts along the surjection $B\to D$, with no claim that $\mathfrak b$ itself is finitely
generated.

12. Consider the $A/I$-linear map $\Psi:B/IB\to(B/IB)^{\oplus n}$, $z\mapsto(h_1z,\ldots,h_nz)$.
Both modules are projective over $A/I$ by the splitting in Step 11. Tensoring with $A/\mathfrak m$
gives the same multiplication-vector map on $D$. It has a nonzero kernel element: an
exact-annihilator witness for $\overline{\mathfrak b}\in\operatorname{Ass}_D(D)$ is killed by
every $\bar h_i$. Every element of the maximal ideal $\mathfrak m/I$ of $A/I$ is nilpotent since
$\sqrt I=\mathfrak m$. If $\Psi$ were injective, [lem-trf-nil-local-projective-injection-pure]
would make its residue-field tensor injective, a contradiction. Choose $0\ne z\in\ker\Psi$ and let
$J=\operatorname{Ann}_B(z)$. We have $IB\subseteq J$ and $h_i\in J$. For every $a\in\mathfrak m$
some power belongs to $I$, so $\mathfrak mB\subseteq\sqrt J$. Therefore $\mathfrak b\subseteq\sqrt
J$. This argument includes $n=0$, when $\Psi$ has zero target.

13. Since $z\ne0$, $J$ is proper. Choose a prime $\mathfrak s$ minimal over $J$ by
[lem-weil-pbc-minimal-prime-over-proper-ideal]. Then $\mathfrak s$ is weakly associated to $B/IB$
by its defining witness $z$, contains $\mathfrak b$, and contracts to $\mathfrak m$ because
$\mathfrak m$ is maximal. Apply only the forward implication already proved in Steps 1--9 to the
flat finitely presented algebra $A\to B$ and the module $A/I$; its tensor with $B$ is $B/IB$. This
yields $\overline{\mathfrak s}\in\operatorname{Ass}_D(D)$. It contains $\overline{\mathfrak b}$,
so maximality from Step 10 gives equality. The fibre-prime bijection
[lem-weil-pbc-fibre-ring-primes-bijection] gives $\mathfrak s=\mathfrak b$. Thus $\mathfrak b$ is
minimal over $\operatorname{Ann}_B(z)$. Under the injection $B/IB\to L\otimes_A B$ of Step 11 its
annihilator stays exactly $J$ (an element kills its image if and only if it kills $z$), proving
weak association to $L\otimes_A B$. The equivalences of Step 10 prove the required reverse
implication in the original rings.
-/
theorem weakly_associated_tensor_iff_of_flat_finitePresentation
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    (M : Type w) [AddCommGroup M] [Module R M]
    (p : PrimeSpectrum R)
    (q : {q : PrimeSpectrum S | PrimeSpectrum.comap (algebraMap R S) q = p}) :
    (∃ z : M ⊗[R] S,
      q.val.asIdeal ∈ ((⊥ : Submodule S (S ⊗[R] M)).colon
        {TensorProduct.comm R M S z}).minimalPrimes) ↔
      (∃ m : M, p.asIdeal ∈ ((⊥ : Submodule R M).colon {m}).minimalPrimes) ∧
      (PrimeSpectrum.preimageOrderIsoFiber R S p q).asIdeal ∈
        RingTheory.annihilatorAssociatedPrimes (p.asIdeal.Fiber S) (p.asIdeal.Fiber S) := by
  sorry

end Module
