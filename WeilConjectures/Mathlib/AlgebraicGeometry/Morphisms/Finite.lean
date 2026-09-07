/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Group.Affine

/-!
# Schemes finite over a field

A scheme `X` finite over a field `K` is affine, and its ring of global sections `Γ(X, ⊤)` is a
finite `K`-module, hence an artinian ring. Since the prime spectrum of an artinian ring is finite
and discrete, `X` is a finite discrete space, all of whose points are closed.

## Main results

- `AlgebraicGeometry.isAffine_of_isFinite_over_field`: a scheme finite over a field is affine.
- `AlgebraicGeometry.module_finite_presheafObj`: `Γ(X, ⊤)` is a finite `K`-module.
- `AlgebraicGeometry.finite_of_isFinite_over_field`,
  `AlgebraicGeometry.discreteTopology_of_isFinite_over_field`,
  `AlgebraicGeometry.isClosed_singleton_of_isFinite_over_field`: `X` is a finite discrete space
  of closed points.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- A scheme finite over a field is affine. -/
lemma isAffine_of_isFinite_over_field (f : X ⟶ Spec (.of K)) [IsFinite f] : IsAffine X :=
  isAffine_of_isAffineHom f

/-- The global sections of a scheme finite over `Spec K` form a finite `K`-module. -/
instance module_finite_presheafObj [X.Over (Spec (.of K))] [IsAffine X]
    [IsFinite (X ↘ Spec (.of K))] : Module.Finite K Γ(X, ⊤) := by
  rw [← RingHom.finite_algebraMap]
  have h : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, ⊤)))) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite X.isoSpec.hom,
      isoSpec_hom_comp_specMap_algebraMap]
    infer_instance
  rwa [IsFinite.SpecMap_iff] at h

/-- The global sections of a scheme finite over a field form an artinian ring. -/
lemma isArtinianRing_presheafObj (K : Type u) [Field K] (X : Scheme.{u})
    [X.Over (Spec (.of K))] [IsAffine X] [IsFinite (X ↘ Spec (.of K))] :
    IsArtinianRing Γ(X, ⊤) :=
  isArtinian_of_tower K inferInstance

/-- A scheme finite over a field has finitely many points. -/
lemma finite_of_isFinite_over_field (f : X ⟶ Spec (.of K)) [IsFinite f] : Finite X := by
  let : X.Over (Spec (.of K)) := ⟨f⟩
  have : IsFinite (X ↘ Spec (.of K)) := ‹IsFinite f›
  have : IsAffine X := isAffine_of_isFinite_over_field f
  have := isArtinianRing_presheafObj K X
  have e : ↥X ≃ₜ PrimeSpectrum Γ(X, ⊤) := Scheme.homeoOfIso X.isoSpec
  exact .of_equiv _ e.toEquiv.symm

/-- A scheme finite over a field is a discrete space. -/
lemma discreteTopology_of_isFinite_over_field (f : X ⟶ Spec (.of K)) [IsFinite f] :
    DiscreteTopology X := by
  let : X.Over (Spec (.of K)) := ⟨f⟩
  have : IsFinite (X ↘ Spec (.of K)) := ‹IsFinite f›
  have : IsAffine X := isAffine_of_isFinite_over_field f
  have := isArtinianRing_presheafObj K X
  have e : ↥X ≃ₜ PrimeSpectrum Γ(X, ⊤) := Scheme.homeoOfIso X.isoSpec
  exact e.isEmbedding.discreteTopology

/-- Every point of a scheme finite over a field is closed. -/
lemma isClosed_singleton_of_isFinite_over_field (f : X ⟶ Spec (.of K)) [IsFinite f] (x : X) :
    IsClosed {x} :=
  have := discreteTopology_of_isFinite_over_field f
  isClosed_discrete _

end AlgebraicGeometry
