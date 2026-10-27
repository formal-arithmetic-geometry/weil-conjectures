/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import WeilConjectures.Mathlib.RingTheory.Henselian

/-! # Relative separable closedness of a dense henselian valued subfield

Source: ILO, Travaux de Gabber, XX 4.4, printed p.374, Krasner argument.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace FieldTheory

/-- A dense henselian valued subfield contains every element of the larger field
that is separable over it. Henselianity of the larger field is unnecessary.
Source: ILO, Travaux de Gabber, XX 4.4, printed p.374, the injectivity-on-extensions
part of the Krasner argument (blueprint: lem-per-dense-henselian-relative-separable-closed).

Proof: If a is already in K there is nothing to prove. Otherwise embed the finite
separable extension K(a) in a separable closure of K and take a finite Galois
extension N containing it. Prolong the henselian valuation of K to N using
lem-per-henselian-finite-extension-topology. Its restriction to K(a) and the
valuation topology inherited from L both induce the given topology on K.
The uniqueness-of-topology clause of that lemma identifies these topologies.
Density in L implies density of K in the subspace K(a). Intersect the open
Krasner neighbourhood of a in N, supplied by lem-per-henselian-krasner-neighbourhood,
with K(a). It contains a and therefore meets K in an element b. The neighbourhood
property gives a in K(b); since b is in K, this is K. This contradicts the initial
assumption and proves the claim. Use the actual value groups when converting
multiplicative valuations to additive valuations, so the ball topologies agree.
The argument includes a=0 and needs neither completeness nor a rank hypothesis. -/
theorem denseHenselian_isSeparable_mem_range
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (Γ : Type v) (Δ : Type w)
    [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]
    [vK : Valued K Γ] [vL : Valued L Δ]
    [vK.v.IsNontrivial] [vL.v.IsNontrivial]
    [HenselianLocalRing vK.v.valuationSubring]
    (h_induced : Topology.IsInducing (algebraMap K L))
    (h_dense : DenseRange (algebraMap K L))
    (a : L) (ha : IsSeparable K a) :
    a ∈ Set.range (algebraMap K L) := by sorry

end FieldTheory
