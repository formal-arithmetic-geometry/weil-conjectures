/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.AlgebraicGeometry.AffinePseudoCoherentPrincipalModel

/-! # Local module models on a finite principal-open cover

Source: Stacks Project, Tag 08E7, finite-cover and local-model steps.
-/

@[expose] public section

universe u wA wX wL

open CategoryTheory

namespace AlgebraicGeometry

/-- A pseudo-coherent associated-sheaf complex has pseudo-coherent module localizations
on a finite principal-open cover. This asserts only the local models, not their gluing
(Stacks, Tags 08E7, 08CB and 08E5). -/
theorem affine_pseudoCoherent_localization_cover (A : Type u) [CommRing A]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ U : (Spec (.of A)).Opens, HasDerivedCategory.{wX}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))]
    [∀ f : A, HasDerivedCategory.{wL} (ModuleCat.{u} (Localization.Away f))]
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (h : Scheme.IsPseudoCoherent (Spec (.of A))
      (DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          _ _ _ _ (tilde.functor (.of A))
          ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj M))) :
    ∃ (r : ℕ) (f : Fin r → A), Ideal.span (Set.range f) = ⊤ ∧
      ∀ i : Fin r, DerivedCategory.IsPseudoCoherent
        (DerivedCategory.Q.obj ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (algebraMap A (Localization.Away (f i))))
          (ComplexShape.up ℤ)).obj M)) := by
  classical
  let S : Set A := {f | DerivedCategory.IsPseudoCoherent
    (DerivedCategory.Q.obj ((Functor.mapHomologicalComplex
      (ModuleCat.extendScalars (algebraMap A (Localization.Away f)))
      (ComplexShape.up ℤ)).obj M))}
  have hpoint : ∀ x : PrimeSpectrum A, ∃ f ∈ S, x ∈ PrimeSpectrum.basicOpen f := by
    intro x
    obtain ⟨U, hx, P, hb, hfree, hiso⟩ := h x
    obtain ⟨V, ⟨f, rfl⟩, hxf, hfU⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp U.isOpen x hx
    exact ⟨f, affine_pseudoCoherent_principal_model A M f U hfU P hb hfree hiso, hxf⟩
  have hspan : Ideal.span S = ⊤ := by
    apply PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mp
    apply top_unique
    intro x _
    obtain ⟨f, hf, hxf⟩ := hpoint x
    have hle : PrimeSpectrum.basicOpen f ≤ ⨆ a ∈ S, PrimeSpectrum.basicOpen a :=
      le_iSup_of_le f (le_iSup_of_le hf le_rfl)
    exact hle hxf
  obtain ⟨t, htS, ht⟩ := (Ideal.span_eq_top_iff_finite S).mp hspan
  let e : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
  let f : Fin (Fintype.card t) → A := fun i => (e i).1
  refine ⟨Fintype.card t, f, ?_, fun i => htS (e i).2⟩
  have hrange : Set.range f = (t : Set A) := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro ha
      exact ⟨e.symm ⟨a, ha⟩, by simp [f]⟩
  rw [hrange]
  exact ht

end AlgebraicGeometry
