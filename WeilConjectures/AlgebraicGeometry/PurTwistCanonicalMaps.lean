/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.NativeIntegralTensorTransport.NativeIntegralTensorTransport
public import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
public import WeilConjectures.TateTwist.ProEtale
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit

/-! # Canonical maps of the condensed pulled-back Tate twists

Source: `literature/blueprint/latest/blueprint/sec-proetale-coefficients/
sk-def-sp-tate-twist/def-coefficient-twists-detailed.md`, clauses (1)--(3)
(blueprint: lem-pur-twist-sheaf-locally-free).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory MonoidalCategory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj
namespace AlgebraicGeometry.ProEtale

open PurityTransport

private theorem integralTateFreeMap_hom
    (S : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] (n : ℕ) :
    (integralTateFreeMap S ell E n).hom =
      integralTateFiniteMap S ell E n ⊗ₘ
        𝟙 (rootsOfUnitySheaf S (ell ^ (n + 1))) := by
  simp only [integralTateFreeMap, Mod.comp_hom', Mod.comapId_inv_app_hom,
    Category.id_comp]
  exact (coefficientFreeTensor_linear
    (𝟙 (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ell]) S))
    (integralTateFiniteMap S ell E n) (integralTateFiniteMap S ell E n)
    (by simp) (𝟙 (rootsOfUnitySheaf S (ell ^ (n + 1))))).exists.choose_spec

private theorem integralTateBaseLeg_hom
    (S : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] (n : ℕ) :
    (integralTateBaseLeg S ell E n).hom = (tateProjection S ell (n + 1)).hom ≫
      (integralTateFiniteMap S ell E n ⊗ₘ
        𝟙 (rootsOfUnitySheaf S (ell ^ (n + 1)))) := by
  simp only [integralTateBaseLeg, Mod.comp_hom', Mod.comapComp_hom_app_hom,
    integralTateFreeMap_hom]
  erw [Category.comp_id]

private theorem integralTateBaseLeg_compatibility
    (S : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] (n : ℕ) :
    (integralTateBaseLeg S ell E (n + 1)).hom ≫
        (coefficientIntegralTwistTransition ell E S n).hom =
      (integralTateBaseLeg S ell E n).hom := by
  let v := eqToHom (by rw [pow_succ'] :
    rootsOfUnitySheaf S (ell ^ (n + 2)) =
      rootsOfUnitySheaf S (ell * ell ^ (n + 1))) ≫
        rootsOfUnitySheafPow S (ell ^ (n + 1)) ell
  have hv : (coefficientIntegralTwistTransition ell E S n).hom =
      coefficientMap (twistFiniteReduction ell E n) S ⊗ₘ v :=
    (coefficientFreeTensor_linear
      (coefficientMap (twistReduction ell E (n + 1)) S)
      (coefficientMap (twistReduction ell E n) S)
      (coefficientMap (twistFiniteReduction ell E n) S)
      (twistReduction_comp ell E S n) v).exists.choose_spec
  have hcoef : integralTateFiniteMap S ell E (n + 1) ≫
      coefficientMap (twistFiniteReduction ell E n) S = integralTateFiniteMap S ell E n := by
    simp only [integralTateFiniteMap, Category.assoc, twistReduction_comp]
  have hp : (tateProjection S ell (n + 2)).hom ≫
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ell]) S) ◁ v =
        (tateProjection S ell (n + 1)).hom := by
    have h := limit.w (tateModuleSystem S ell) (homOfLE (Nat.le_succ (n + 1))).op
    simp only [tateModuleSystem, Functor.ofOpSequence_map_homOfLE_succ] at h
    exact congrArg Mod.Hom.hom h
  rw [integralTateBaseLeg_hom, integralTateBaseLeg_hom, hv]
  rw [Category.assoc, tensorHom_comp_tensorHom, hcoef, Category.id_comp]
  rw [← hp, Category.assoc]
  simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp,
    Category.comp_id]

/-- The globally defined scalar-adjoint legs form a cone.
Source: coefficient twists, projection-induced comparison, step 3
(blueprint: lem-pur-integral-tate-leg-compatible).
Proof: the free linear maps have underlying tensor coefficient maps. The coefficient
quotients commute, and the Tate limit projections commute with the root-power
transition. Thus the base legs commute; the scalar adjunction transports this equality
to the integral legs. -/
theorem integralTateLeg_compatible
    (S : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] :
    integralTateLegCompatibilityStatement S ell E := by
  intro n
  change (integralTateLeg S ell E (n + 1) ≫
    coefficientIntegralTwistTransition ell E S n).hom = _
  congr 1
  apply Mod.extendScalarsObj_hom_ext'
  simp only [Mod.comp_hom', integralTateLeg]
  change Mod.extendUnitHom (integralTateCoefficientMap S ell E) (tateModule S ell) ≫
      ((Mod.extendHom (integralTateCoefficientMap S ell E)
        (integralTateBaseLeg S ell E (n + 1))).hom ≫
          (coefficientIntegralTwistTransition ell E S n).hom) =
    Mod.extendUnitHom (integralTateCoefficientMap S ell E) (tateModule S ell) ≫
      (Mod.extendHom (integralTateCoefficientMap S ell E)
        (integralTateBaseLeg S ell E n)).hom
  erw [Mod.extendUnitHom_extendHom_assoc, Mod.extendUnitHom_extendHom]
  exact integralTateBaseLeg_compatibility S ell E n

end AlgebraicGeometry.ProEtale
