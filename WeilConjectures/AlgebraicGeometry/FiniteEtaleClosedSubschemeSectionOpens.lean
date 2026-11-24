/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

import WeilConjectures.AlgebraicGeometry.AffineEtaleClosedImmersionLift
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
/-- An affine étale scheme over a closed subscheme of an affine integral normal scheme with
separably closed function field is covered by finitely many pairwise disjoint clopen opens,
each mapping to the closed subscheme by an open immersion (Stacks, Tag 09ZA). -/
theorem Etale.exists_finite_clopen_opens_of_closedImmersion
    {X Z V : Scheme.{u}} [IsAffine X] [IsIntegral X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    [IsSepClosed X.functionField] (i : Z ⟶ X) [IsClosedImmersion i]
    (p : V ⟶ Z) [Etale p] [IsAffine V] :
    ∃ (n : ℕ) (W : Fin n → V.Opens),
      (∀ j, IsClosed (W j : Set V)) ∧
      (∀ j k, j ≠ k → Disjoint (W j) (W k)) ∧
      (⨆ j, W j) = ⊤ ∧ ∀ j, IsOpenImmersion ((W j).ι ≫ p) := by
  classical
  obtain ⟨U, hU, q, hq, a, ha⟩ := Etale.exists_affine_lift_of_closedImmersion i p
  let : IsAffine U := hU
  let : Etale q := hq
  obtain ⟨ι, hfin, O, hdisj, hcov, hopen⟩ :=
    Etale.exists_finite_opens_isOpenImmersion_of_isSepClosed_functionField
      (fun x ↦ (hX x).2) q
  let : Finite ι := hfin
  let : Fintype ι := Fintype.ofFinite ι
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hclosed (j : ι) : IsClosed (O j : Set U) := by
    have heq : (O j : Set U)ᶜ = ⋃ k : {k : ι // k ≠ j}, (O k.1 : Set U) := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_iUnion]
      constructor
      · intro hx
        have hx' : x ∈ (⨆ k, O k) := by rw [hcov]; trivial
        obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
        exact ⟨⟨k, fun h ↦ hx (h ▸ hk)⟩, hk⟩
      · rintro ⟨k, hk⟩ hj
        exact (Set.disjoint_left.mp (show Disjoint (O k.1 : Set U) (O j : Set U) from
          TopologicalSpace.Opens.coe_disjoint.mpr (hdisj k.1 j k.2))) hk hj
    rw [← isOpen_compl_iff, heq]
    exact isOpen_iUnion fun k ↦ (O k.1).isOpen
  refine ⟨Fintype.card ι, fun j ↦ a ⁻¹ᵁ O (e j), ?_, ?_, ?_, ?_⟩
  · intro j
    exact (hclosed (e j)).preimage a.continuous
  · intro j k hjk
    rw [disjoint_iff]
    change a ⁻¹ᵁ (O (e j) ⊓ O (e k)) = ⊥
    rw [(hdisj (e j) (e k) (fun h ↦ hjk (e.injective h))).eq_bot]
    rfl
  · rw [← a.preimage_iSup, e.iSup_comp, hcov, a.preimage_top]
  · intro j
    have H := (isPullback_morphismRestrict a (O (e j))).paste_vert ha
    let : IsOpenImmersion ((O (e j)).ι ≫ q) := hopen (e j)
    exact MorphismProperty.of_isPullback H inferInstance
end AlgebraicGeometry
