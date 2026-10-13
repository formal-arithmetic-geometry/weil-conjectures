/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M4
-/
module

public import Sheaf.AlgebraicGeometry.CoefficientIntersectionRingData
public import Sheaf.AlgebraicGeometry.FiniteAffineCechCoefficientComparisonMap
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.FiniteAffineCechIntersectionBaseChange
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections

/-! # Affine coefficient intersection computation

Source: Stacks Project, Tags 0097, 01I9, 01IA and 02KG.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Affine pullback sections, before the ring pushout and tensor contraction.
Source: Stacks Project, Tags 0097, 01I9 and 01IA.
(blueprint: aux-pc-coefficient-intersection-section-model).

Proof: The intersection I = W intersect f' inverse image B is affine by the
intersection base-change theorem. Restrict F to the affine open Z of f inverse
image U. Apply the affine pullback sections theorem to the restricted lift
X' -> f inverse image U on Z and I. Compare tensorPullback with pullback by
uniqueness of left adjoints, and compare open-immersion pullback with
restriction. Pullback composition identifies the resulting module with M|I.
The conjugate-isomorphism unit equation and restriction naturality identify
the image of the restricted pullback-unit generator with 1 tensor s.
The inverse of the affine sections comparison is the required map, linear
for the intersection ring. Empty intersections satisfy the same formula. -/
theorem exists_coefficientIntersection_section_model
    {X T : Scheme.{u}} (f : X ⟶ T) [IsSeparated f]
    (F : X.Modules) [F.IsQuasicoherent]
    (U : T.Opens) (hU : IsAffineOpen U)
    (Z : (f ⁻¹ᵁ U).toScheme.Opens) (hZ : IsAffineOpen Z)
    {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
    (sq : IsPullback g' f' f (g ≫ U.ι))
    (W : X'.Opens) (hW : W = g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ Z))
    (B : T'.Opens) (hB : IsAffineOpen B) :
    let D := Γ((f ⁻¹ᵁ U).toScheme, Z)
    let S := Γ(X', W ⊓ f' ⁻¹ᵁ B)
    let : Algebra D S := (coefficientIntersectionRingMap f U Z g g' f' sq W hW B).toAlgebra
    let M := (pullback g').obj F
    ∃ e : Γ(M, W ⊓ f' ⁻¹ᵁ B) →ₗ[S]
        (S ⊗[D] Γ(F.restrict (f ⁻¹ᵁ U).ι, Z)),
      ∀ s : Γ(F.restrict (f ⁻¹ᵁ U).ι, Z),
        e (M.presheaf.map (homOfLE (inf_le_left : W ⊓ f' ⁻¹ᵁ B ≤ W)).op
          (coefficientPullbackGenerator F (f ⁻¹ᵁ U) Z g' W hW s)) =
        (1 : S) ⊗ₜ[D] s := by sorry
end
end AlgebraicGeometry.Scheme.Modules
