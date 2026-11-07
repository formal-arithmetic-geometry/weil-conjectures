/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.CompletedMatchingRingMap
public import Mathlib.RingTheory.AdicCompletion.LocalRing
import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.CompletedMatchingResidueQuotientSurjective

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

private theorem residue_lift_of_quotient_surjective
    {R S : Type u} [CommRing R] [CommRing S]
    (g : R →+* S) (I : Ideal S)
    (h : Function.Surjective (fun a : R => Ideal.Quotient.mk I (g a))) :
    ∀ b : S, ∃ a : R, g a - b ∈ I := by
  intro b
  obtain ⟨a, ha⟩ := h (Ideal.Quotient.mk I b)
  refine ⟨a, ?_⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub]
  exact sub_eq_zero.mpr ha

/-- Every completed section lifts modulo the extended maximal ideal.
Source: Stacks Project, Tags 0BLH and 05ER, applied to the residue quotient.
(blueprint: lem-sbc-completed-matching-ring-map-residue-lift)

Proof in words: Choose generators f_i of the maximal ideal of A. Their principal
opens cover U, including the empty-cover case when A is Artinian. The finite
restrictions of q supply affine algebras B_i and their transition isomorphisms;
s supplies the finite completion algebra B'. The overlap identifies B'_f_i
with B_i tensor_A C, giving the module gluing datum of 05ER. The sheaf equalizer
identifies its H0 with the ring of matching pairs. Completion is flat and gives
an isomorphism modulo the maximal ideal. Proposition 05ER identifies the
canonical scalar extension of H0 with B', compatibly with its projection to B'.
Reducing this identification modulo m_C B' gives a surjective map from H0
scalar-extended to the residue field onto B'/m_C B'. Lift a representative of
any class along the quotient map from H0 tensor_A C. The comparison sends this
lift to the prescribed class: by the projection and C-linearity it is precisely
completedRingMap. Thus their difference lies in m_C B'. No choice of an
algebraization object is used in any definition. For empty U the equalizer is
B' and the Artinian completion is A. If B' is zero the sole section lifts as zero. -/
theorem completedRingMap_residue_lift
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) :
    ∀ b : Γ(E, ⊤), ∃ a, D.completedRingMap a - b ∈
      (IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A)).map
        (((ΓSpecIso (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))).inv ≫
          s.appTop).hom) := by
  let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let I : Ideal (Γ(E, ⊤)) := (IsLocalRing.maximalIdeal C).map
    (((ΓSpecIso (.of C)).inv ≫ s.appTop).hom)
  have hq := D.completedRingMap_residue_quotient_surjective hU
  intro b
  exact residue_lift_of_quotient_surjective D.completedRingMap.hom I hq b

end AlgebraicGeometry.Scheme.CompletionGluingData
