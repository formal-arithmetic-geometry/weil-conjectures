/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistData

/-! Restriction compatibility for normalized scalar-extension twist sections.
(blueprint: lem-sfb-proj-scalar-extension-twist-section-restriction). -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

/-- The normalized scalar-extension section commutes with restriction to a smaller open.
Source: the naturality of the comparison morphism and of the tensor-pullback section.
Proof: expand `scalarExtensionTwistSection`; apply naturality of the comparison morphism
and the defining naturality of `tensorPullbackSection`, then evaluate at the given point.
(blueprint: lem-sfb-proj-scalar-extension-twist-section-restriction). -/
theorem scalarExtensionTwistSection_restrict
    {A B : Type u} [CommRing A] [CommRing B]
    {σ τ : Type u} [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (r : Proj ℬ ⟶ Proj 𝒜)
    (θ : ∀ j : ℤ, (tensorPullback r).obj (twist 𝒜 j) ≅ twist ℬ j)
    (j : ℤ) (U V : (Proj 𝒜).Opens) (e : V ≤ U)
    (s : Γ(twist 𝒜 j, U)) (x : r ⁻¹ᵁ V) :
    (scalarExtensionTwistSection r θ j V
      ((twist 𝒜 j).presheaf.map (homOfLE e).op s)).1 x =
      (scalarExtensionTwistSection r θ j U s).1
        ⟨x.1, Scheme.Hom.preimage_mono r e x.2⟩ := by
  sorry

end AlgebraicGeometry.Proj
