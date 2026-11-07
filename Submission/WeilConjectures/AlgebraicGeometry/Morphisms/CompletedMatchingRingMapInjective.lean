/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.CompletedMatchingRingMap
import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.CompletedMatchingRingMapKernelTorsion
import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.CompletedMatchingRingMapTorsionKernel

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Injectiveity of completed matching sections

Source: Stacks Project, Tags 0BLH, 05ER and 05EU.
(blueprint: lem-sbc-completed-matching-ring-map-injective)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- The completed matching-ring comparison is injective.
Source: Stacks Project, Tag 05ER, kernel argument; Tags 0BLH and 05EU.
(blueprint: lem-sbc-completed-matching-ring-map-injective)

Proof in words: Choose finitely many generators f_i of the maximal ideal.
Their principal opens cover U
by hU. Since q and s are finite, their restrictions are affine, giving finite
algebras B_i and B' = Γ(E). The supplied overlap identifies (B')_{f_i} with
B_i tensor_A C, and the transition maps of q supply the cocycle. The equalizer
for Γ(Y) identifies matchingRing with H⁰ of this gluing object. Completion is
flat and A/m → C/mC is an isomorphism. In the proof of Tag 05ER, localization
makes the kernel of the canonical comparison a system (K,0,0,0). H⁰ is left
exact and H⁰ of the comparison is bijective, so K = 0. Thus the comparison
H⁰ tensor_A C → B' is injective. Tag 05EU identifies the underlying module
map with completedRingMap, since both take a matching pair tensor c to c times
its second component. For empty U the Noetherian local ring is Artinian and
its completion is A; the comparison is the identity under the affine counit.
Empty E or Y causes no exception: all equalizers and zero modules obey the
same kernel argument. -/
theorem completedRingMap_injective
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) :
    Function.Injective D.completedRingMap := by
  apply (injective_iff_map_eq_zero D.completedRingMap.hom).mpr
  intro x hx
  obtain ⟨n, hn⟩ := D.completedRingMap_kernel_torsion hU x hx
  exact D.completedRingMap_torsion_kernel_zero hU x n hn hx

end AlgebraicGeometry.Scheme.CompletionGluingData
