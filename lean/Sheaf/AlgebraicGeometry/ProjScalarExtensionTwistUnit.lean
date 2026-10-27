/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistData

/-! Degree-zero unit part of the normalized scalar-extension twist laws.
(blueprint: lem-sfb-proj-scalar-extension-twist-fraction-laws-unit). -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

/- The degree-zero fraction formula is the structural pullback map. -/
theorem scalarExtension_twist_unit
    {A B : Type u} [CommRing A] [CommRing B]
    {σ τ : Type u} [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (ψ : 𝒜 →+*ᵍ ℬ) (r : Proj ℬ ⟶ Proj 𝒜)
    (θ : ∀ j : ℤ, (tensorPullback r).obj (twist 𝒜 j) ≅ twist ℬ j)
    (hθ : IsScalarExtensionTwistComparison ψ r θ) :
    ∀ (U : (Proj 𝒜).Opens) (s : Γ(Proj 𝒜, U)),
      scalarExtensionTwistSection r θ 0 U
        (Scheme.Modules.Hom.app (unitToTwistZero (𝒜 := 𝒜)) U s) =
        Scheme.Modules.Hom.app (unitToTwistZero (𝒜 := ℬ)) (r ⁻¹ᵁ U) (r.app U s) := by
  sorry

end AlgebraicGeometry.Proj
