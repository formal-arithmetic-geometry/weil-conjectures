/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistData

/-! Multiplication part of the normalized scalar-extension twist laws.
(blueprint: lem-sfb-proj-scalar-extension-twist-fraction-laws-multiplication). -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

/- The chartwise fraction calculation proves this product clause. -/
theorem scalarExtension_twist_multiplication
    {A B : Type u} [CommRing A] [CommRing B]
    {σ τ : Type u} [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (ψ : 𝒜 →+*ᵍ ℬ) (r : Proj ℬ ⟶ Proj 𝒜)
    (θ : ∀ j : ℤ, (tensorPullback r).obj (twist 𝒜 j) ≅ twist ℬ j)
    (hθ : IsScalarExtensionTwistComparison ψ r θ) :
    ∀ (i j : ℤ) (U : (Proj 𝒜).Opens)
      (s : Γ(twist 𝒜 i, U)) (t : Γ(twist 𝒜 j, U))
      (v : Γ(twist 𝒜 (i + j), U)),
      (∀ x : U, (v.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
        (s.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) * t.1 x) →
      ∀ x : r ⁻¹ᵁ U,
        ((scalarExtensionTwistSection r θ (i + j) U v).1 x :
          Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
        ((scalarExtensionTwistSection r θ i U s).1 x :
          Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) *
        (scalarExtensionTwistSection r θ j U t).1 x := by
  sorry

end AlgebraicGeometry.Proj
