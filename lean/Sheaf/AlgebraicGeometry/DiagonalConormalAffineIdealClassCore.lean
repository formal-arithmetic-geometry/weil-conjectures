/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module
public import Sheaf.AlgebraicGeometry.DiagonalConormal
public import Mathlib.RingTheory.Kaehler.Basic
/-! # Affine diagonal tensor chart and kernel sections

Source: Stacks Project, Tags 08S2, 01KJ and 01R3.
(blueprint: stage3-diagonal-conormal-affine-ideal-class-core).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry
variable {X S : Scheme.{u}}
/-- Core affine tensor-product ring calculation for the diagonal chart.
(blueprint: stage3-diagonal-conormal-affine-ideal-class-core)
Source: Stacks Project, Tags 08S2, 01KJ.
Proof: Put A = Γ(X,U), R = Γ(S,V), B = A ⊗[R] A, and J = ker μ.
The restricted morphism U → V has affine source and target. Its self-fibre product
embeds as W = p₁⁻¹U ∩ p₂⁻¹U, because equality over S of two points mapping into V
is equality over V. The affine fibre-product construction is Spec B; the two ring
maps are a ↦ a ⊗ 1 and a ↦ 1 ⊗ a. Applying affine global sections gives r and
both projection formulas. The diagonal pulls W back to U and is induced by μ.
The actual kernel sheaf restricts to the kernel of O_W → δ_*O_U: open restriction
preserves kernels and pushforward along δ is computed on inverse images of opens.
On the affine chart this morphism on sections is μ in the coordinates r, so its
sectionwise kernel contains r(j) for every j ∈ J. The universal property of the
module-sheaf kernel supplies the required section s. Empty U gives the zero ring
and zero section modules, and the construction still applies. -/
theorem diagonalConormal_affine_ideal_class_core (f : X ⟶ S)
    (U : X.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    letI : Algebra Γ(S, V.1) Γ(X, U.1) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
    let W := (pullback.fst f f) ⁻¹ᵁ U.1 ⊓ (pullback.snd f f) ⁻¹ᵁ U.1
    ∃ r : (Γ(X, U.1) ⊗[Γ(S, V.1)] Γ(X, U.1)) ≃+* Γ(pullback f f, W),
      (∀ a : Γ(X, U.1), r ((1 : Γ(X, U.1)) ⊗ₜ[Γ(S, V.1)] a) =
        (pullback.snd f f).appLE U.1 W inf_le_right a) ∧
      (∀ a : Γ(X, U.1), r (a ⊗ₜ[Γ(S, V.1)] (1 : Γ(X, U.1))) =
        (pullback.fst f f).appLE U.1 W inf_le_left a) ∧
      ∀ j : KaehlerDifferential.ideal Γ(S, V.1) Γ(X, U.1),
        ∃ s : Γ(kernel (SheafOfModules.unitToPushforwardObjUnit
            (pullback.diagonal f).toRingCatSheafHom), W),
          (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
            (pullback.diagonal f).toRingCatSheafHom)).val.app (op W) s = r j := by sorry
end AlgebraicGeometry
