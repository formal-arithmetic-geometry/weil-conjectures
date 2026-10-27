/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.Paper.SmoothOrientationCoefficientFamily
public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.Paper.AdicUnitTraceReductionData
import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexDual
import Sheaf.Paper.CoefFiniteHomSiteDescent
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-! # Site exchange comparisons under the smooth orientation

Source: latest blueprint, sec-six-functors/sk-thm-sf-package,
thm-pod-global-verdier-duality.proof.md, second paragraph
(blueprint: def-pod-normalized-coefficient-units).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

attribute [local instance 2000] IntermediateField.algebra'
attribute [local instance 2000] ConstructibleExceptionalCoefficients.category
attribute [local irreducible] CategoryTheory.Functor.mapIso CategoryTheory.Iso.trans

/-- The actual coefficient unit in its recorded finite-Tor domain. This reuses the
finite-unit membership proof of the reduction theorem, without assuming membership
as an extra hypothesis.
Source: finite reduction of purity, coefficient-unit specialization
(blueprint: def-pod-normalized-coefficient-units). -/
def smoothOrientationCoefficientUnit (P : PurityFiniteSetting.{u})
    (W : Scheme.{u}) [W.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of P.field.k))]
    [QuasiCompact (W ↘ Spec (.of P.field.k))]
    [IsSeparated (W ↘ Spec (.of P.field.k))] :
    finiteTorConstructibleCategory P.coefficients.l P.extension P.level P.level_pos W :=
  let F (r : {r : ℕ // 1 ≤ r}) : Prop :=
    let _ := Padic.finite_coefficientExtensionRing P.coefficients.l P.extension r r.property
    finiteTorConstructible P.coefficients.l P.extension r r.property W
      ((ProEtale.finiteCoefficientIntrinsicComparison W
        (Padic.coefficientExtensionRing P.coefficients.l P.extension r)).mapDerivedCategory.obj
          (Etale.ordinaryFiniteUnit
            (ULift.{u + 1} (Padic.coefficientExtensionRing P.coefficients.l P.extension r)) W))
  let hAll (r : ℕ) (hr : 1 ≤ r) : F ⟨r, hr⟩ := by
    cases r with
    | zero => exact False.elim (Nat.not_succ_le_zero 0 hr)
    | succ n =>
      let A := ULift.{u + 1}
        (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
      let : Finite (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1)) :=
        Padic.finite_coefficientExtensionRing _ _ _ (Nat.succ_pos n)
      let U := Etale.ordinaryFiniteUnit A W
      have hU : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) W U :=
        (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) W).prop_of_iso
          (((_root_.DerivedCategory.singleFunctor _ 0).mapIso
            (Functor.Monoidal.εIso
              (constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} A))).symm) ≪≫
            _root_.DerivedCategory.singleFunctorObjUnitIso _).symm
          (Etale.constructibleFiniteTor_unit A)
      have hEt : finiteTorConstructibleEtale P.coefficients.l P.extension
          (n + 1) (Nat.succ_pos n) W U := by
        obtain ⟨⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩, c, d, ht⟩ := hU
        refine ⟨⟨fun i ↦
          (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc i),
          min a b, b, min_le_right _ _, ?_⟩, min c d, d, min_le_right _ _, ?_⟩
        · intro i hi
          rcases hi with hi | hi
          · exact (_root_.DerivedCategory.isGE_iff U a).1 ha i
              (hi.trans_le (min_le_left _ _))
          · exact (_root_.DerivedCategory.isLE_iff U b).1 hb i hi
        · exact Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
            (ht.mono (min_le_left _ _) le_rfl)
      exact ((coefFiniteHomSiteDescent P.field P.coefficients.l
        P.coefficients.different P.extension W).1 n).2.2.2.2 U hEt |>.1
  let ν := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) W
  let E := ProEtale.finiteCoefficientIntrinsicRealization W P.Ring
  letI : E.Additive := ProEtale.finiteCoefficientIntrinsicRealization_additive W P.Ring
  letI : CategoryTheory.Limits.PreservesFiniteLimits E :=
    ProEtale.finiteCoefficientIntrinsicRealization_preservesFiniteLimits W P.Ring
  letI : CategoryTheory.Limits.PreservesFiniteColimits E :=
    ProEtale.finiteCoefficientIntrinsicRealization_preservesFiniteColimits W P.Ring
  let V : finiteTorConstructibleCategory P.coefficients.l P.extension P.level P.level_pos W :=
    ⟨(ν ⋙ E).mapDerivedCategory.obj (Etale.ordinaryFiniteUnit P.Coefficient W),
      hAll P.level P.level_pos⟩
  smoothOrientationFiniteTorTransport P W V (P.coefficientUnit W)
    ((Functor.mapDerivedCategoryCompIso ν E).app (Etale.ordinaryFiniteUnit P.Coefficient W))

/-- The coefficient unit of the fixed six-functor datum, viewed in the finite-Tor
domain through its recorded normalization. The actual datum unit, rather than an
unused datum parameter, is the argument of the finite smooth-purity equations.
Source: six-functor finite-unit normalization
(blueprint: def-pod-normalized-coefficient-units). -/
def smoothOrientationDatumUnit (P : PurityFiniteSetting.{u})
    (S : SixFunctorOperationDatum P.field P.coefficients P.extension P.level P.level_pos) :
    finiteTorConstructibleCategory P.coefficients.l P.extension P.level P.level_pos
      (Spec (.of P.field.k)) :=
  smoothOrientationFiniteTorTransport P (Spec (.of P.field.k))
    (smoothOrientationCoefficientUnit P (Spec (.of P.field.k)))
    S.finiteDuality.unit.obj
    (PurityFiniteSetting.finiteReductionUnitModel P.Ring (Spec (.of P.field.k)) ≪≫
      S.finiteUnit.symm)

/-- The integral coefficient unit at a literal finite subfield of the fixed closure.
It is the degree-zero completed coefficient line, rather than an arbitrary integral
object or a freely chosen lift of its finite reductions.
Source: purity conventions and normalized reconstruction
(blueprint: def-pod-normalized-coefficient-units). -/
def smoothOrientationIntegralUnit (P : PurityFiniteSetting.{u})
    (E : AdicPurityScalarNaturality.Field P.field P.coefficients) :=
  AdicSmoothDualizing.integralTwist
    (RationalSmoothPurityCanonical.stageSetting P E)
    (Spec (.of P.field.k)) (𝟙 _) 0

/-- The source of the specified integral unit component is the actual shifted
Tate line. Pullback of the regular unit uses the recorded normalized tower map;
the remaining factor is the exact twist's scalar unitor and even shift.
Source: normalized completed-unit pullback and unit trace source identification
(blueprint: def-pod-normalized-coefficient-units). -/
@[irreducible] def smoothIntegralUnitSourceIso
    (P : PurityFiniteSetting.{u}) {X : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    (aX : X ⟶ Spec (.of P.field.k)) [aX.IsOver (Spec (.of P.field.k))]
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    (d : ℕ) [SmoothOfRelativeDimension d aX]
    (E : AdicPurityScalarNaturality.Field P.field P.coefficients)
    (core : CompletedUnitPullback.Core P.coefficients.l E.val aX) :
    (PurUnitTrace.sourceFunctor P.field P.coefficients E.val aX d).obj
        (smoothOrientationIntegralUnit P E).obj ≅
      (AdicSmoothDualizing.integralTwist (RationalSmoothPurityCanonical.stageSetting P E)
        X (X ↘ Spec (.of P.field.k)) d).obj :=
  (PurUnitTrace.sourceFunctor P.field P.coefficients E.val aX d).mapIso
      ((shiftFunctorZero _ ℤ).app _) ≪≫
    PurUnitTrace.sourceUnitIso P.field P.coefficients E.val aX d core

end WeilConjectures
