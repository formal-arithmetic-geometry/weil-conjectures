/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.CanonicalCoefficientWeilCohomology
import WeilConjectures.AlgebraicGeometry.RegularCoefficientCoherentReduction
import WeilConjectures.AlgebraicGeometry.IntegralSystemReductionFullyFaithful

/-! # Vanishing cohomology of the coefficient shifted Tate constant -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.ConstantPurityFrobenius

attribute [local instance 1100] CategoryTheory.instOverClass

namespace WeilConjectures.NativeCoefficientCohomology

variable (P : PurityFiniteSetting.{u})
  (X₀ : Over (Spec (.of P.field.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

local instance tateVanishingPointFiniteType : LocallyOfFiniteType (point P.field).hom :=
  inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of P.field.k₀))))
local instance tateVanishingPointQuasiCompact : QuasiCompact (point P.field).hom :=
  inferInstanceAs (QuasiCompact (𝟙 (Spec (.of P.field.k₀))))
local instance tateVanishingSourceFiniteType :
    LocallyOfFiniteType ((P.field.geometricFiber X₀).left ↘ Spec (.of P.field.k)) :=
  (FrobeniusExchange.fiber_finiteType P.field X₀).1
local instance tateVanishingSourceQuasiCompact :
    QuasiCompact ((P.field.geometricFiber X₀).left ↘ Spec (.of P.field.k)) :=
  (FrobeniusExchange.fiber_finiteType P.field X₀).2
local instance tateVanishingTargetFiniteType :
    LocallyOfFiniteType ((P.field.geometricFiber (point P.field)).left ↘
      Spec (.of P.field.k)) :=
  (FrobeniusExchange.fiber_finiteType P.field (point P.field)).1
local instance tateVanishingTargetQuasiCompact :
    QuasiCompact ((P.field.geometricFiber (point P.field)).left ↘ Spec (.of P.field.k)) :=
  (FrobeniusExchange.fiber_finiteType P.field (point P.field)).2
local instance tateVanishingSourceUnits : ∀ x : (P.field.geometricFiber X₀).left,
    Invertible (P.coefficients.l : (P.field.geometricFiber X₀).left.residueField x) :=
  fun x ↦ sfWeilPrimeInvertible P.field P.coefficients.l P.coefficients.different X₀ x
local instance tateVanishingTargetUnits : ∀ x : (P.field.geometricFiber (point P.field)).left,
    Invertible (P.coefficients.l :
      (P.field.geometricFiber (point P.field)).left.residueField x) :=
  fun x ↦ sfWeilPrimeInvertible P.field P.coefficients.l P.coefficients.different
    (point P.field) x

/-- The canonical coefficient shifted Tate constant has zero cohomology away from
its concentration degree. This statement concerns only the coefficient Weil heart.

Source: BBD 1.3, standard truncations; the canonical purity source and scalar-unit
identification in lem-pur-constant-purity-frobenius-square.
(blueprint: lem-sf-coefficient-twisted-constant-vanishing)

Proof: faithful coherent reduction identifies the regular completed coefficient and
reconstructed tensor unit, because both reduce to the coherent system unit. Rationalize
and include this isomorphism at the least coefficient stage. Compose sourceUnit,
tensoring with this unit comparison, and the tensor right unitor. The inclusion's
shift comparison identifies the result with the unshifted coefficient root line shifted
by 2d. That root line lies in the standard heart, so the source has both bounds -2d.
If n is smaller, truncLE n vanishes. If n is larger, truncLE n retains the upper bound
-2d, and its truncGE n vanishes. The subsequent shift preserves this zero object.
Faithful forgetting makes every Hom to or from this cohomology pair a subsingleton.
The available zero arrows therefore exhibit it as a zero object. The argument also treats
d=0 and empty schemes; it requires no smoothness or native realization. -/
theorem coefficient_twisted_constant_vanishing (d : ℕ) (n : ℤ)
    (hn : n ≠ -2 * (d : ℤ)) :
    IsZero ((canonicalCoefficientWeilCohomology P X₀ n).obj
        (twistedConstant P X₀ d)) := by
  let D := P.field
  let l := P.coefficients.l
  let hl := P.coefficients.different
  let Ω := P.coefficients.Qbar
  let X := (D.geometricFiber X₀).left
  let t := sfCommonStageStandardTStructure l X Ω D hl
  let K := (FrobeniusCoefficientTwists.commonWeilLine D l hl X₀ Ω (d : ℤ)).carrier
  let M := (twistedConstant P X₀ d).carrier
  have hK := FrobeniusCoefficientTwists.commonWeilLine_heart D l hl X₀ Ω (d : ℤ)
  rw [← (sfCommonStageHeart_properties l X Ω D hl).1] at hK
  change t.heart K at hK
  rw [t.mem_heart_iff] at hK
  have : t.IsLE K 0 := hK.1
  have : t.IsGE K 0 := hK.2
  have hunit : Nonempty (unit P.field P.coefficients.l P.coefficients.different
      P.coefficients.Qbar (P.field.geometricFiber X₀).left ≅
        pullbackTensorCommonUnit P.coefficients.l P.coefficients.Qbar
          (P.field.geometricFiber X₀).left) := by
    let E₀ := AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l
      P.coefficients.Qbar (Padic.finiteCoefficientBase P.coefficients.l P.coefficients.Qbar)
    let R := integralSystemReduction P.coefficients.l E₀ (P.field.geometricFiber X₀).left
    have := (integralSystemReduction_fullyFaithful P.coefficients.l E₀
      (P.field.geometricFiber X₀).left).1
    have := (integralSystemReduction_fullyFaithful P.coefficients.l E₀
      (P.field.geometricFiber X₀).left).2
    obtain ⟨a⟩ := regularCoefficient_coherentReduction P.coefficients.l E₀
      (P.field.geometricFiber X₀).left
    let b : R.obj (constantWeilIntegralObject P.coefficients.l E₀ P.field
        P.coefficients.different (P.field.geometricFiber X₀).left) ≅
        R.obj (pullbackTensorIntegralUnit P.coefficients.l E₀
          (P.field.geometricFiber X₀).left) :=
      a ≪≫ (pullbackTensorIntegralUnitReduction P.coefficients.l E₀
        (P.field.geometricFiber X₀).left).symm
    let c := R.preimageIso b
    exact ⟨(GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := P.coefficients.l) (Ω := P.coefficients.Qbar)
      (Y := (P.field.geometricFiber X₀).left)
      (Padic.finiteCoefficientBase P.coefficients.l P.coefficients.Qbar)).mapIso
        ((sfRationalConstructibleLocalization P.coefficients.l E₀
          (P.field.geometricFiber X₀).left).mapIso c)⟩
  obtain ⟨u⟩ := hunit
  let e : M ≅ K⟦2 * (d : ℤ)⟧ :=
    sourceUnit P.field P.coefficients.l P.coefficients.different P.coefficients.Qbar
      X₀ (point P.field) (pointMap P.field X₀) d ≪≫
      (commonStageDerivedTensor P.coefficients.l P.coefficients.Qbar
        (P.field.geometricFiber X₀).left).mapIso (Iso.prod (Iso.refl _) u) ≪≫
      pullbackTensorCommonRightUnitor P.coefficients.l P.coefficients.Qbar
        (P.field.geometricFiber X₀).left
        (shiftedLine P.field P.coefficients.l P.coefficients.different
          P.coefficients.Qbar X₀ d) ≪≫
      ((GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := P.coefficients.l) (Ω := P.coefficients.Qbar)
        (Y := (P.field.geometricFiber X₀).left)
        (Padic.finiteCoefficientBase P.coefficients.l P.coefficients.Qbar)).commShiftIso
          (2 * (d : ℤ))).app _
  have : t.IsLE (K⟦2 * (d : ℤ)⟧) (-2 * (d : ℤ)) :=
    t.isLE_shift K 0 (2 * (d : ℤ)) (-2 * (d : ℤ)) (by omega)
  have : t.IsGE (K⟦2 * (d : ℤ)⟧) (-2 * (d : ℤ)) :=
    t.isGE_shift K 0 (2 * (d : ℤ)) (-2 * (d : ℤ)) (by omega)
  have : t.IsLE M (-2 * (d : ℤ)) := t.isLE_of_iso e.symm _
  have : t.IsGE M (-2 * (d : ℤ)) := t.isGE_of_iso e.symm _
  have hz : IsZero ((constructibleTruncationCohomology t n).obj M) := by
    by_cases h : n < -2 * (d : ℤ)
    · have : t.IsGE M (n + 1) := t.isGE_of_ge M (n + 1) (-2 * (d : ℤ)) (by omega)
      exact (shiftFunctor _ n).map_isZero ((t.truncGE n).map_isZero
        (t.isZero_truncLE_obj_of_isGE n (n + 1) rfl M))
    · have : t.IsLE ((t.truncLE n).obj M) (n - 1) :=
        t.isLE_of_le _ (-2 * (d : ℤ)) (n - 1) (by omega)
      exact (shiftFunctor _ n).map_isZero
        (t.isZero_truncGE_obj_of_isLE (n - 1) n (by omega) _)
  let F := ((sfCommonStageHeartProperty l X Ω).inverseImage
    (sfCommonStageWeilForget D l hl X₀ Ω)).ι ⋙ sfCommonStageWeilForget D l hl X₀ Ω
  have : F.Faithful := by
    dsimp [F, sfCommonStageWeilForget]
    infer_instance
  let Z := (canonicalCoefficientWeilCohomology P X₀ n).obj (twistedConstant P X₀ d)
  have hZ : IsZero (F.obj Z) := hz
  constructor
  · intro Y
    exact ⟨⟨⟨0⟩, fun f ↦ F.map_injective (hZ.eq_of_src _ _)⟩⟩
  · intro Y
    exact ⟨⟨⟨0⟩, fun f ↦ F.map_injective (hZ.eq_of_tgt _ _)⟩⟩

end WeilConjectures.NativeCoefficientCohomology
