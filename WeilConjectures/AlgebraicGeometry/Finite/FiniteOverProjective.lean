/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.FiniteMorphism
import WeilConjectures.AlgebraicGeometry.ProjectiveSpaceFiniteIndexIso

/-! # Finite covers of projective schemes over affine opens

The conclusion uses the affine-local H-projective convention.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

private theorem finite_over_projective_embedding_affine {S T Y : Scheme.{u}} [IsAffine S]
    (p : T ⟶ S) [IsHProjective p] (h : Y ⟶ T) [IsFinite h] :
    ∃ (N : ℕ) (i : Y ⟶ ℙ(ULift.{u} (Fin (N + 1)); S)),
      IsClosedImmersion i ∧ i ≫ ℙ(ULift.{u} (Fin (N + 1)); S) ↘ S = h ≫ p := by
  classical
  obtain ⟨n, hn, j, hj, hjp⟩ := IsHProjective.exists_isClosedImmersion (f := p)
  obtain ⟨m, hm, k, hk, hkp⟩ :=
    ProjectiveSpace.exists_isClosedImmersion_of_isFinite p j hjp h
  cases isEmpty_or_nonempty m with
  | inl hempty =>
    have : IsEmpty Y := ⟨fun y ↦ isEmptyElim (k y)⟩
    exact ⟨0, isInitialOfIsEmpty.to _, inferInstance, isInitialOfIsEmpty.hom_ext _ _⟩
  | inr hnonempty =>
    obtain ⟨N, e, he, _⟩ := ProjectiveSpace.exists_finite_index_iso m S
    exact ⟨N, k ≫ e.hom, inferInstance, by rw [Category.assoc, he, hkp]⟩

/-- Over each affine open of a Noetherian base, a finite cover of a projective scheme
admits a closed immersion into a finite-dimensional projective space over that open. -/
theorem finite_over_projective_affineLocally {S T Y : Scheme.{u}}
    [CompactSpace S] [IsLocallyNoetherian S] (p : T ⟶ S) [IsProjective p]
    (h : Y ⟶ T) [IsFinite h] :
    (∀ (U : S.Opens), IsAffineOpen U →
      (∃ (N : ℕ) (i : ((h ≫ p) ⁻¹ᵁ U).toScheme ⟶
          ℙ(ULift.{u} (Fin (N + 1)); U.toScheme)),
        IsClosedImmersion i ∧
          i ≫ ℙ(ULift.{u} (Fin (N + 1)); U.toScheme) ↘ U.toScheme = (h ≫ p) ∣_ U) ∧
      IsProjective ((h ≫ p) ∣_ U)) ∧
    (IsAffine S → IsProjective (h ≫ p)) := by
  have haff : ∀ {B C D : Scheme.{u}} [IsAffine B] (q : C ⟶ B) [IsHProjective q]
      (g : D ⟶ C) [IsFinite g], IsProjective (g ≫ q) := by
    intro B C D _ q _ g _
    obtain ⟨N, i, hi, hiq⟩ := finite_over_projective_embedding_affine q g
    have : IsHProjective (g ≫ q) := ⟨⟨ULift.{u} (Fin (N + 1)), inferInstance, i, hi, hiq⟩⟩
    exact IsHProjective.isProjective _
  constructor
  · intro U hU
    have : IsAffine U.toScheme := hU
    obtain ⟨n, hn, j, hj, hjp⟩ := IsHProjective.exists_isClosedImmersion (f := p)
    have hw : (p ∣_ U) ≫ U.ι = ((p ⁻¹ᵁ U).ι ≫ j) ≫ ℙ(n; S) ↘ S := by
      rw [morphismRestrict_ι, Category.assoc, hjp]
    let k := ProjectiveSpace.liftBaseChange (p ∣_ U) ((p ⁻¹ᵁ U).ι ≫ j) hw
    have : IsClosedImmersion k := by
      apply MorphismProperty.of_isPullback
        (ProjectiveSpace.isPullback_liftBaseChange (p ∣_ U)
          (show IsPullback (p ⁻¹ᵁ U).ι (p ∣_ U) (j ≫ ℙ(n; S) ↘ S) U.ι from
            hjp.symm ▸ (isPullback_morphismRestrict p U).flip) hw)
      infer_instance
    have : IsHProjective (p ∣_ U) :=
      ⟨⟨n, hn, k, inferInstance, ProjectiveSpace.liftBaseChange_over _ _ hw⟩⟩
    rw [morphismRestrict_comp]
    exact ⟨finite_over_projective_embedding_affine (p ∣_ U) (h ∣_ p ⁻¹ᵁ U),
      haff (p ∣_ U) (h ∣_ p ⁻¹ᵁ U)⟩
  · intro hS
    have : IsAffine S := hS
    exact haff p h

end AlgebraicGeometry
