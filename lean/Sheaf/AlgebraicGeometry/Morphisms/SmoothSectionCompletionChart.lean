/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Sheaf.RingTheory.Smooth.AugmentationCompletionPowerSeries

/-!
# Flat completion chart for a smooth section over a local base

Source: Stacks Project, Tags 0EYB, 05D5 and 00MB.
(blueprint: lem-sbc-smooth-section-completion-chart)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A smooth section over a Noetherian local ring has a flat power-series chart,
compatible with both its structure map and the entire section.

Source: Stacks Project, Tag 0EYB, the completion paragraph; Tags 05D5 and 00MB.
(blueprint: lem-sbc-smooth-section-completion-chart)

Proof: Choose an affine neighbourhood of the section's closed-point value. Its
inverse image under the section is an open containing the closed point of the
local spectrum, hence the whole spectrum. Factor the section through this affine
neighbourhood. Its algebra C is smooth over B and its augmentation C to B splits
the structure map. Put I equal to the augmentation kernel. By 05D5, I/I^2 is a
finite projective B-module, hence free over the local ring B. Choose a basis and
lifts in I. The resulting map from B[[X_1,...,X_n]] to the I-adic completion is an
isomorphism: modulo I^2 it is an isomorphism, formal smoothness lifts its inverse
successively modulo I^k, and passage to the inverse limit gives an inverse.
The chosen lifts lie in I, so evaluation at zero corresponds to the augmentation.
Since C is a finite type algebra over the Noetherian ring B it is Noetherian, and
its completion map is flat by 00MB. Compose its spectrum map with the affine open
immersion. The B-algebra structure proves the first equality, and compatibility
of the augmentation proves the second. For n = 0 the same argument has no basis
vectors and identifies the completion with B. -/
theorem exists_smooth_section_completion_chart
    (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of B)) [Smooth p]
    (s : Spec (.of B) ⟶ X) (hs : s ≫ p = 𝟙 _) :
    ∃ (n : ℕ) (t : Spec (.of (MvPowerSeries (Fin n) B)) ⟶ X), Flat t ∧
      t ≫ p = Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := Fin n))) ∧
      Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin n))) ≫
        t = s := by
  classical
  obtain ⟨C, i, hi, hx, -⟩ :=
    exists_affine_mem_range_and_range_subset
      (X := X) (U := ⊤) (x := s (IsLocalRing.closedPoint B)) (by trivial)
  let : IsOpenImmersion i := hi
  have hrange : Set.range s ⊆ Set.range i := by
    rintro _ ⟨x, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint x).map s.continuous).mem_open
      i.isOpenEmbedding.isOpen_range hx
  let s' := IsOpenImmersion.lift i s hrange
  have hs' : s' ≫ i = s := IsOpenImmersion.lift_fac i s hrange
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (i ≫ p)
  obtain ⟨ε, hε⟩ := Spec.map_surjective s'
  let : Algebra B C := φ.hom.toAlgebra
  have hsm : RingHom.Smooth φ.hom := by
    rw [← HasRingHomProperty.Spec_iff (P := @Smooth), hφ]
    infer_instance
  let : Algebra.Smooth B C := hsm
  have hsplit : ε.hom.comp φ.hom = RingHom.id B := by
    have hcat : φ ≫ ε = 𝟙 _ := by
      apply Spec.map_injective
      rw [Spec.map_comp, hφ, hε, ← Category.assoc, hs', hs, Spec.map_id]
    exact congrArg CommRingCat.Hom.hom hcat
  let εa : C →ₐ[B] B :=
    { ε.hom with commutes' := fun b ↦ congrArg (fun f : B →+* B ↦ f b) hsplit }
  obtain ⟨n, e, he⟩ := Algebra.exists_augmented_completion_powerSeries B C εa
  let I := RingHom.ker εa.toRingHom
  let f : C →+* MvPowerSeries (Fin n) B :=
    e.toRingHom.comp (algebraMap C (AdicCompletion I C))
  let : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing B C
  have hf : f.Flat :=
    (RingHom.flat_algebraMap_iff.mpr (inferInstance :
      Module.Flat C (AdicCompletion I C))).comp (.of_bijective e.bijective)
  let : Flat (Spec.map (CommRingCat.ofHom f)) := Flat.SpecMap_iff.mpr hf
  refine ⟨n, Spec.map (CommRingCat.ofHom f) ≫ i, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, ← hφ, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    change e (algebraMap C (AdicCompletion I C) (algebraMap B C b)) = _
    rw [← IsScalarTower.algebraMap_apply B C (AdicCompletion I C), e.commutes]
    rfl
  · rw [← Category.assoc, ← Spec.map_comp]
    have hfe : CommRingCat.ofHom f ≫
        CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin n)) = ε := by
      apply CommRingCat.hom_ext
      exact RingHom.ext he
    rw [hfe, hε, hs']

end AlgebraicGeometry.Scheme
