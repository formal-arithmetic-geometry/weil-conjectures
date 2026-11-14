/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.DiagonalConormal
public import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
/-! # Affine diagonal tensor chart and kernel sections

## References

* Stacks Project, Tags 08S2, 01KJ and 01R3
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry
variable {X S : Scheme.{u}}
/-- Core affine tensor-product ring calculation for the diagonal chart (Stacks, Tags 08S2 and 01KJ).
-/
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
            (pullback.diagonal f).toRingCatSheafHom)).val.app (op W) s = r j := by
  let : Algebra Γ(S, V.1) Γ(X, U.1) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
  let W := (pullback.fst f f) ⁻¹ᵁ U.1 ⊓ (pullback.snd f f) ⁻¹ᵁ U.1
  let H := IsPullback.of_hasPullback f f
  have : IsIso (pushoutSection H hUV hUV (show W = _ from rfl)) :=
    isIso_pushoutSection_of_isAffineOpen H hUV hUV rfl V.2 U.2 U.2
  have hp : IsPushout (f.appLE V.1 U.1 hUV) (f.appLE V.1 U.1 hUV)
      ((pullback.fst f f).appLE U.1 W inf_le_left)
      ((pullback.snd f f).appLE U.1 W inf_le_right) :=
    (isIso_pushoutSection_iff H hUV hUV rfl).mp inferInstance
  let e : CommRingCat.of (Γ(X, U.1) ⊗[Γ(S, V.1)] Γ(X, U.1)) ≅
      Γ(pullback f f, W) :=
    IsColimit.coconePointUniqueUpToIso
      (CommRingCat.pushoutCoconeIsColimit Γ(S, V.1) Γ(X, U.1) Γ(X, U.1)) hp.isColimit
  let r := e.commRingCatIsoToRingEquiv
  have hr₂ (a : Γ(X, U.1)) : r (1 ⊗ₜ[Γ(S, V.1)] a) =
      (pullback.snd f f).appLE U.1 W inf_le_right a := by
    exact ConcreteCategory.congr_hom
      (IsColimit.comp_coconePointUniqueUpToIso_hom
        (CommRingCat.pushoutCoconeIsColimit Γ(S, V.1) Γ(X, U.1) Γ(X, U.1))
        hp.isColimit WalkingSpan.right) a
  have hr₁ (a : Γ(X, U.1)) : r (a ⊗ₜ[Γ(S, V.1)] 1) =
      (pullback.fst f f).appLE U.1 W inf_le_left a := by
    exact ConcreteCategory.congr_hom
      (IsColimit.comp_coconePointUniqueUpToIso_hom
        (CommRingCat.pushoutCoconeIsColimit Γ(S, V.1) Γ(X, U.1) Γ(X, U.1))
        hp.isColimit WalkingSpan.left) a
  refine ⟨r, hr₂, hr₁, ?_⟩
  let δ := pullback.diagonal f
  let φ := SheafOfModules.unitToPushforwardObjUnit δ.toRingCatSheafHom
  have hcomp : (pullback.snd f f).appLE U.1 W inf_le_right ≫ δ.app W =
      (pullback.fst f f).appLE U.1 W inf_le_left ≫ δ.app W := by
    rw [δ.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.appLE_comp_appLE]
    simp [δ]
  have hker : KaehlerDifferential.ideal Γ(S, V.1) Γ(X, U.1) ≤
      RingHom.ker ((δ.app W).hom.comp r.toRingHom) := by
    rw [← KaehlerDifferential.span_range_eq_ideal, Ideal.span_le]
    rintro _ ⟨a, rfl⟩
    change δ.app W (r (1 ⊗ₜ[Γ(S, V.1)] a - a ⊗ₜ[Γ(S, V.1)] 1)) = 0
    rw [map_sub, hr₂, hr₁, map_sub]
    exact sub_eq_zero.mpr (ConcreteCategory.congr_hom hcomp a)
  intro j
  have hj : (SheafOfModules.evaluation (pullback f f).ringCatSheaf (op W)).map φ
      (r j) = 0 := by
    change δ.app W (r j) = 0
    exact hker j.property
  have hj' : r j ∈ Set.range
      ((SheafOfModules.evaluation (pullback f f).ringCatSheaf (op W)).map
        (kernel.ι φ)) := by
    rw [Scheme.Modules.range_map_kernelι]
    exact hj
  exact hj'
end AlgebraicGeometry
