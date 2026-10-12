/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.RingTheory.Depth
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.QuotSMulTop
import Sheaf.RingTheory.DepthLeSupportDimension

/-!
# Good elements for a maximal regular sequence

Source: Stacks Project, Algebra, Lemma 10.103.2 (Tag 00N4), the preceding
notation in Section 10.103 (Tag 00N2), and Definition 10.103.1 (Tag 00N3)
(blueprint: lem-weil-pbc-cm-module-good-sequence-element-nonzerodivisor).
-/

@[expose] public section

universe u v

namespace Module

/-- A good element for a maximal regular sequence on a nonzero finite Cohen–Macaulay
module of positive dimension is regular; its quotient is Cohen–Macaulay of dimension
one less, with the indicated initial segment as a maximal regular sequence.
Source: Stacks Project, Algebra, Tag 00N4 and its preceding notation, Tag 00N3
(blueprint: lem-weil-pbc-cm-module-good-sequence-element-nonzerodivisor).

Here `fs` lists `f₁, …, f_d`. Cohen–Macaulayness is written as equality of depth
and support dimension. Goodness is the displayed dimension condition on the support
intersected with the zero locus of `g :: fs.take i`. Dimension uses the inherited
prime-ideal inclusion order, including negative infinity for the empty set.

Proof (the node's eight steps):
1. Identify successive quotients with the quotient by all the listed elements
(def-weil-pbc-quotient-module). They remain finite. Their support is the original
support intersected with the corresponding zero locus
(lem-weil-pbc-support-quotient-ideal-module). A nonzero finite module over a local
ring has its maximal ideal in its support: an element outside that ideal is a unit,
so cannot kill a nonzero element upon localization (def-weil-pbc-module-localization).
An e-term regular sequence in the maximal ideal gives depth at least e by
(def-weil-pbc-depth); if support dimension is e, the opposite bound
(lem-weil-pbc-depth-le-support-dimension) makes the module Cohen–Macaulay.
Induct on positive e for all modules, sequences, and good elements of dimension e.
2. At e = 1, let K be the kernel of multiplication by g. It is finite
(lem-weil-pbc-noetherian-submodule-finite). Goodness at i = 0 and locality force
Supp(M) ∩ V(g) to be the singleton maximal ideal: any smaller prime would give a
chain of length one. Localization shows Supp(K) is contained in this intersection:
a nonzero localized kernel element remains nonzero in M, and its prime contains g.
3. If K were nonzero, its support would contain the maximal ideal, which would be
minimal in its support. The associated-prime lemma
(lem-weil-pbc-minimal-support-prime-associated) provides a nonzero kernel element
annihilated by that ideal. In particular f₁ kills it, contradicting regularity of
f₁ on M (def-weil-pbc-regular-sequence). Thus K = 0, proving injectivity.
This is the node's associated-prime version of the source's finite-length argument.
4. The quotient by g has support exactly that singleton, hence is nonzero of
support dimension zero. Its empty sequence is regular. Its depth is zero by the
support-dimension bound, so it is Cohen–Macaulay. This proves the base case.
5. For d ≥ 2 put M' = M/f₁M. Regularity of f₁ gives support dimension d - 1
(lem-weil-pbc-support-dimension-quotient-element-equality). Successive-quotient
identifications show f₂, …, f_d is regular on M'. It is nonzero, finite, and
Cohen–Macaulay by the depth bounds from step 1.
6. The support-quotient formula identifies the goodness condition for M' and
f₂, …, f_d at j with the original condition at i = j + 1. Thus g is good for M'.
7. Induction gives injectivity of g on M' and a Cohen–Macaulay double quotient,
with regular sequence f₂, …, f_{d-1}. Its final quotient is nonzero, so f₁, g is
regular on M. Permuting this pair
(lem-weil-pbc-regular-sequence-permutation-noetherian-local) makes g, f₁ regular;
hence g is injective on M and f₁ is injective on M/gM.
8. The remaining elements f₂, …, f_{d-1} are regular on the successive quotients
of M/gM by induction and the quotient identifications. The final quotient is
nonzero by induction, so this entire initial segment is regular. Goodness at i = 0
and the support-quotient formula give dimension d - 1. The depth bounds give depth
d - 1, establishing Cohen–Macaulayness and maximality of the initial segment. -/
theorem isSMulRegular_of_good_sequence {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (M : Type v) [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Nontrivial M]
    (d : ℕ) (hd : 1 ≤ d)
    (hcm : (IsLocalRing.depth (R := R) M : WithBot ℕ∞) = supportDim R M)
    (hdim : supportDim R M = ((d : ℕ∞) : WithBot ℕ∞))
    (fs : List R) (hlen : fs.length = d)
    (hmem : ∀ f ∈ fs, f ∈ IsLocalRing.maximalIdeal R)
    (hreg : RingTheory.Sequence.IsRegular M fs)
    (g : R) (hg : g ∈ IsLocalRing.maximalIdeal R)
    (hgood : ∀ i : ℕ, i < d →
      Order.krullDim ((Module.support R M ∩
        PrimeSpectrum.zeroLocus {x : R | x ∈ g :: fs.take i}) : Set (PrimeSpectrum R)) =
          (((d - i - 1 : ℕ) : ℕ∞) : WithBot ℕ∞)) :
    IsSMulRegular M g ∧
      (IsLocalRing.depth (R := R) (QuotSMulTop g M) : WithBot ℕ∞) =
        supportDim R (QuotSMulTop g M) ∧
      IsLocalRing.depth (R := R) (QuotSMulTop g M) = (d - 1 : ℕ) ∧
      supportDim R (QuotSMulTop g M) = (((d - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) ∧
      RingTheory.Sequence.IsRegular (QuotSMulTop g M) (fs.take (d - 1)) := by
  sorry

end Module
