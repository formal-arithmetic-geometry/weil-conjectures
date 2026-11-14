/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SelfTorAffineSection
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import WeilConjectures.AlgebraicGeometry.SelfTorAffineChartSections
import WeilConjectures.AlgebraicGeometry.LocallyQuasicoherentAffinePullbackSections

/-! # Affine sections of the chart model after tensor pullback

Source: Stacks Project, Tags 01I9 and 0096.

## Implementation details

The comparison in `exists_selfTor_affine_tensor_sections` is built locally on the affine
open `U` (via the affine pullback comparison between `U` and its preimage), so it needs
neither quasi-coherence of the pushforward on all of `Y` nor quasi-separatedness of `Y`. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
open scoped TensorProduct
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

/-- For an affine morphism `i : Z ⟶ Y` and an affine open `U`, the sections over `i⁻¹ U` of
the tensor pullback of the chart model of `M` are `Γ(Z, i⁻¹ U) ⊗[Γ(Y, U)] M`, via an
isomorphism sending `b ⊗ m` to `b • selfTorAffineSection i U M m`.
Stacks Project, Tags 01I9, 01I7 and 0096. -/
theorem exists_selfTor_affine_tensor_sections
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsAffineHom i]
    (U : Y.affineOpens) (M : ModuleCat.{u} (Γ(Y, U.1) : Type u)) :
    letI : Algebra Γ(Y, U.1) Γ(Z, i ⁻¹ᵁ U.1) := (i.app U.1).hom.toAlgebra
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
      Scheme.Modules.pushforward U.1.ι ⋙ Scheme.Modules.tensorPullback i
    ∃ e : (Γ(Z, i ⁻¹ᵁ U.1) ⊗[Γ(Y, U.1)] M) ≃ₗ[Γ(Z, i ⁻¹ᵁ U.1)]
        (T.obj M).val.obj (op (i ⁻¹ᵁ U.1)),
      ∀ (b : Γ(Z, i ⁻¹ᵁ U.1)) (m : M),
        e (b ⊗ₜ[Γ(Y, U.1)] m) = b • selfTorAffineSection i U M m := by
  classical
  dsimp only
  let : Algebra Γ(Y, U.1) Γ(Z, i ⁻¹ᵁ U.1) := (i.app U.1).hom.toAlgebra
  let L := (tilde.functor Γ(Y, U.1)).obj M
  let C := (Scheme.Modules.pushforward U.1.ι).obj
    ((Scheme.Modules.restrictFunctor U.2.isoSpec.hom).obj L)
  obtain ⟨e₀, hC, he₀⟩ := exists_selfTor_affine_chart_sections U M
  obtain ⟨e₁, he₁⟩ := exists_locallyQuasicoherent_affine_pullback_sections i U C hC
  let e := TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl Γ(Z, i ⁻¹ᵁ U.1) Γ(Z, i ⁻¹ᵁ U.1)) e₀
  refine ⟨e.trans e₁, ?_⟩
  intro b m
  change e₁ (b ⊗ₜ[Γ(Y, U.1)] e₀ m) = _
  rw [he₁, he₀]
  rfl

end AlgebraicGeometry
