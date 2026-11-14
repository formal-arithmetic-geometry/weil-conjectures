/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DiagonalConormal
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.RingTheory.Kaehler.Basic
import WeilConjectures.AlgebraicGeometry.DiagonalConormalAffineIdealClassCore
import WeilConjectures.AlgebraicGeometry.DiagonalConormalAffineIdealClassQ

/-! # The affine diagonal ideal class map

## References

* Stacks Project, Tags 08S2, 01KJ and 01R3
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry
variable {X S : Scheme.{u}}

/-- On an affine diagonal chart the tensor multiplication kernel maps onto the
actual conormal sections, compatibly with the canonical tensor-pullback unit.
This statement is independent of any normalized derivation (Stacks, Tags 08S2, 01KJ and 01R3). -/
theorem diagonalConormal_affine_ideal_class (f : X ⟶ S)
    (U : X.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    letI : Algebra Γ(S, V.1) Γ(X, U.1) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
    let W := (pullback.fst f f) ⁻¹ᵁ U.1 ⊓ (pullback.snd f f) ⁻¹ᵁ U.1
    ∃ (r : (Γ(X, U.1) ⊗[Γ(S, V.1)] Γ(X, U.1)) ≃+* Γ(pullback f f, W))
      (q : KaehlerDifferential.ideal Γ(S, V.1) Γ(X, U.1) →ₗ[Γ(X, U.1)]
        Γ(diagonalConormal f, U.1)),
      Function.Surjective q ∧
      (∀ a : Γ(X, U.1), r ((1 : Γ(X, U.1)) ⊗ₜ[Γ(S, V.1)] a) =
        (pullback.snd f f).appLE U.1 W inf_le_right a) ∧
      (∀ a : Γ(X, U.1), r (a ⊗ₜ[Γ(S, V.1)] (1 : Γ(X, U.1))) =
        (pullback.fst f f).appLE U.1 W inf_le_left a) ∧
      ∀ (hδ : U.1 ≤ (pullback.diagonal f) ⁻¹ᵁ W)
        (j : KaehlerDifferential.ideal Γ(S, V.1) Γ(X, U.1)),
        ∃ s : Γ(kernel (SheafOfModules.unitToPushforwardObjUnit
            (pullback.diagonal f).toRingCatSheafHom), W),
          (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
            (pullback.diagonal f).toRingCatSheafHom)).val.app (op W) s = r j ∧
          q j = (diagonalConormal f).presheaf.map (homOfLE hδ).op
            (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
              (pullback.diagonal f))).unit.app
                (kernel (SheafOfModules.unitToPushforwardObjUnit
                  (pullback.diagonal f).toRingCatSheafHom))).val.app (op W) s) := by
  let : Algebra Γ(S, V.1) Γ(X, U.1) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
  obtain ⟨r, hr₂, hr₁, hlift⟩ := diagonalConormal_affine_ideal_class_core f U V hUV
  obtain ⟨e, he⟩ := diagonalConormal_affine_ideal_class_q f U V hUV r hr₂ hr₁
  let q := e.toLinearMap.comp
    ((KaehlerDifferential.fromIdeal Γ(S, V.1) Γ(X, U.1)).restrictScalars Γ(X, U.1))
  refine ⟨r, q, e.surjective.comp
    (KaehlerDifferential.fromIdeal_surjective Γ(S, V.1) Γ(X, U.1)), hr₂, hr₁, ?_⟩
  intro hδ j
  obtain ⟨s, hs⟩ := hlift j
  exact ⟨s, hs, he hδ j s hs⟩

end AlgebraicGeometry
