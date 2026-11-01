/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedLineTensorOrdinaryData
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison

/-! # Completed scalar tensor sections and the base action

Source: blueprint sk-def-sp-tate-twist-locally-free, Proof (3).
(blueprint: lem-pur-completed-line-scalar-base-smul)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct MonoidalCategory
universe t u
namespace WeilConjectures
namespace CompletedLineTensor
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted completedCoefficientMap
  completedOrdinaryScalarExtension completedScalarTensorSection
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] F)

/-- Scalar tensor sections respect the coefficient-module action: for the completed
coefficient map `φ`, `s ⊗ (r • x) = φ(r) • (s ⊗ x)` in the ordinary extension.
Source: Stacks 03EK; blueprint
literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-trace-map-of-affine-space/sk-prop-an/sk-def-sp-tate-twist-locally-free.md,
Proof (3), scalar compatibility
(blueprint: lem-pur-completed-line-scalar-base-smul).
Proof: `completedScalarTensorSection` is the sheafification image of the presheaf pure
tensor `s ⊗ₜ x` over the ring map `φ_U`, transported along the canonical equality of
the ordinary extension with `changeOfRings`. In the extension of scalars the tensor is
balanced, so `s ⊗ₜ (r • x) = (s * φ_U r) ⊗ₜ x = φ_U r • (s ⊗ₜ x)`. The sheafification
unit and the `eqToHom` transport are module maps over the target coefficient sections,
hence they carry this identity to the stated one. -/
theorem completed_scalar_base_smul (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
    (r : (completedIntegralCommRingSheafUnrestricted l E X).obj.obj U)
    (x : M.val.obj U) :
    completedScalarTensorSection l E F ι X M U s (smul l E X M U r x) =
      smul l F X ((completedOrdinaryScalarExtension l E F ι X).obj M) U
        ((completedCoefficientMap l E F ι X).hom.app U r)
        (completedScalarTensorSection l E F ι X M U s x) := by sorry

end CompletedLineTensor
end WeilConjectures
