/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistData

/-! # Basis of image standard opens under scalar extension

Source: Stacks Project, constructions.tex, Tag 01N2.
(blueprint: lem-sfb-proj-scalar-extension-image-basic-open-basis).

The positive homogeneous standard opens in the target whose equations come from the
source form a basis when every homogeneous piece of the target is spanned by those
images. This is the geometric input needed to pass from the complete-chart
calculation to arbitrary opens.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Proj

/-- Image standard opens form a basis of the target Proj under the graded spanning
hypothesis.

Source: Stacks Project, constructions.tex, Tag 01N2.
Proof: refine the positive homogeneous standard-open basis using the spanning hypothesis.
Every homogeneous target element is a finite S-linear combination of images; at a prime,
a nonzero sum has a nonzero summand, so one image standard open refines each neighborhood.
The irrelevant-ideal inclusion supplies the covering condition.
(blueprint: lem-sfb-proj-scalar-extension-image-basic-open-basis). -/
theorem scalarExtension_image_basicOpen_isBasis
    {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra S B]
    (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule S B)
    [GradedRing 𝒜] [GradedRing ℬ]
    (β : TensorProduct R S A ≃ₐ[S] B) (ψ : 𝒜 →+*ᵍ ℬ)
    (hβψ : ∀ a : A, β (TensorProduct.tmul R (1 : S) a) = ψ a)
    (hgraded : ∀ n : ℕ, ℬ n = Submodule.span S (ψ '' (𝒜 n : Set A)))
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ HomogeneousIdeal.map ψ
      (HomogeneousIdeal.irrelevant 𝒜)) :
    TopologicalSpace.Opens.IsBasis (Set.range
      (fun i : Σ n : PNat, 𝒜 (n : ℕ) ↦ basicOpen ℬ (ψ (i.2 : A)))) := by
  sorry

end AlgebraicGeometry.Proj
