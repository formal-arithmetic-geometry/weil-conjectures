/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.CompletedMatchingRingMap

/-! # CompletedMatchingRingMapTorsionKernel

Source: Stacks Project, Tags 0BLH, 05ER and 05EU.
(blueprint: lem-sbc-completed-matching-ring-map-torsion-kernel)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- The comparison kills no nonzero maximal-ideal-power torsion element.
Source: Stacks Project, Tag 05ER, torsion-submodule base-change kernel argument.
Proof: put m = maximalIdeal A, C = its completion, and B = D.matchingRing.
The ring-pushout universal property identifies the source with C tensor_A B;
the structural A-action in the hypothesis is its usual scalar action, and
completedRingMap sends c tensor b to c times the second coordinate of b.
Completion is flat and A/m to C/mC is an isomorphism. Since m is finitely
generated, 05EC (1), formalized by Ideal.primaryComponent_baseChange_bijective,
writes the given m-power torsion element x as 1 tensor b for an m-power
torsion b in B. The exponent killing b need not be the supplied exponent n.
The kernel hypothesis says the completed coordinate of b is zero.
Choose generators f_i of m. The opens D(f_i) cover U; their inverse images
in Y are affine because q is finite. Restrict the punctured coordinate of b
to each such inverse image. Some power of f_i kills this restriction, while
f_i is invertible there, so every restriction is zero. The sheaf's separatedness
on this cover makes the punctured coordinate zero. The ring pullback defining
B has jointly injective projections, so b = 0 and hence x = 0.
If U is empty, Y is empty and its ring of sections is zero; only the completed
coordinate is needed. For n = 0 the hypothesis already gives x = 0 by a = 1.
Zero component rings obey the same calculations.
(blueprint: lem-sbc-completed-matching-ring-map-torsion-kernel) -/
theorem completedRingMap_torsion_kernel_zero
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) :
    ∀ x (n : ℕ),
      (∀ a ∈ IsLocalRing.maximalIdeal A ^ n,
        (D.baseMap ≫ pushout.inl _ _).hom a * x = 0) →
      D.completedRingMap x = 0 → x = 0 := by sorry

end AlgebraicGeometry.Scheme.CompletionGluingData
