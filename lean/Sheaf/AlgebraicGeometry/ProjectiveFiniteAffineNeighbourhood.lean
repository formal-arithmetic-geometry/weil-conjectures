/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology

/-!
# Affine neighbourhoods of finite sets in projective schemes

Source: Stacks Project, Tag 01ZY; graded prime avoidance, Tag 00JS.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A scheme admitting an affine morphism into projective space over an affine base has an
 affine open containing any finite set of its points. In particular this applies to a closed
 immersion into projective space over a field.

Proof: map the finite set to the integral projective spectrum. Graded prime avoidance supplies
 a homogeneous form of positive degree missing all these primes. Its basic open is affine.
 The projection from relative projective space to the integral model is affine over an affine
 base, so pulling this open back twice gives the required affine open.

Source: Stacks Project, Tags 01ZY and 00JS.
(blueprint: lem-pd-projective-finite-affine-neighbourhood) -/
theorem exists_isAffineOpen_of_finite_projective {S X : Scheme.{u}} [IsAffine S]
    {α : Type u} (j : X ⟶ ℙ(α; S)) [IsAffineHom j] (s : Set X) (hs : s.Finite) :
    ∃ U : X.Opens, IsAffineOpen U ∧ s ⊆ U := by
  classical
  let ρ := j ≫ ProjectiveSpace.toProjInt α S
  have : IsAffineHom (ProjectiveSpace.toProjInt α S) :=
    MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ inferInstance
  have : IsAffineHom ρ := inferInstance
  let 𝒜 := MvPolynomial.homogeneousSubmodule α (ULift.{u} ℤ)
  let := MvPolynomial.gradedAlgebra (σ := α) (R := ULift.{u} ℤ)
  obtain ⟨d, hd, G, hG, hGs⟩ :=
    ProjectiveSpectrum.exists_homogeneous_notMem_of_finset (hs.toFinset.image ρ)
  refine ⟨ρ ⁻¹ᵁ Proj.basicOpen 𝒜 G, (Proj.isAffineOpen_basicOpen 𝒜 G hG hd).preimage ρ, ?_⟩
  intro x hx
  exact hGs (ρ x) (Finset.mem_image_of_mem ρ (hs.mem_toFinset.mpr hx))

end AlgebraicGeometry
