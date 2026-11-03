/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.RationalSmoothPurityCanonical.RationalSmoothPurityCanonical
public import WeilConjectures.DeligneLaumon.FieldShriekCompositionQcqs
public import WeilConjectures.DeligneLaumon.FieldWeilShriekShiftData
public import WeilConjectures.SmoothPurity.IntegralSystemRealization.IntegralOperationShiftData
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.SixFunctors.RationalPurityCoherence.RationalPurityCommonComparisons
import WeilConjectures.SmoothPurity.FrobeniusCoefficientTwists.FrobeniusCoefficientTwistsCanonical
import WeilConjectures.SmoothPurity.PurityFiniteSetting.SchemeGeometricFrobenius
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
import WeilConjectures.SixFunctors.Orientation.OrientationIntegralCoefficientTwists
import WeilConjectures.SmoothPurity.Integral.Twist.IntegralTwistBaseChange
import WeilConjectures.SmoothPurity.Supporting.SignedTwistReductionComparison
import WeilConjectures.SixFunctors.CanonicalTate.CanonicalTateScalarComparisons
import WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage

/-! # Rational purity: TraceCoherence

Source: current blueprint, rational purity trace and coherence construction.
Existing declarations are retained in this compilation subdivision.
(blueprint: prop-pur-rational-purity-trace-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
open WeilConjectures

attribute [-instance] integralOperationsSiteSmall
  integralReductionSiteEssentiallySmall
attribute [local irreducible] IntegralOnSlice.completion IntegralOnSlice.completionComparison
  IntegralOnSlice.completionUnit IntegralOnSlice.roosUnit IntegralAmbient.tensorTowerIso
  IntegralOnSlice.tower IntegralOnSlice.augmentation
  integralOperationsTensorTowerFunctor IntegralSystemRealization.tensorShifts

attribute [local irreducible] sfIntegralConstructible finiteTorConstructibleIntegral
  completedIntegralCoefficientSheafUnrestricted
  AlgebraicGeometry.Scheme.residueField
  PurCompactSupport.image sfIntrinsicModuleEquivalence ProEtale.comparisonUpperStar
  IntegralOnSlice.duality integralDerivedPullback integralCompletedTensor
  sfRationalScalarExtension HasDerivedCategory.standard SheafOfModules.monoidalCategory
  Iso.trans Iso.prod Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors Functor.leftAdjoint
attribute [local instance 5000] integralTowerHasDerivedCategory scalarReductionTargetDerived
attribute [local irreducible] ScalarLocalization.composition ScalarLocalization.transportHom

namespace WeilConjectures.RationalPurityCoherence
open FrobeniusCoefficientTwists RationalSmoothPurityCanonical

attribute [local irreducible] integralSource integralTraceTranspose rationalSourceComparison
  smallModelIso rationalIso commonIso

attribute [local irreducible] rationalSource commonSource commonSourceComparison
  commonStageDerivedTensor completedIntegralCommRingSheafUnrestricted
attribute [local irreducible] commonStageDerivedPullback

section Trace
attribute [local irreducible] ScalarLocalization.category
attribute [local instance 3000] commonModelField commonModelAlgebra commonModelFinite
attribute [local instance 2000] IntermediateField.algebra'
attribute [local instance 2000] ConstructibleExceptionalCoefficients.category
open ConstructibleExceptionalCoefficients
open AlgebraicallyClosedCoefficients GeneralAlgebraicallyClosedCoefficients
variable (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [∀ x : X, Invertible (P.coefficients.l : X.residueField x)]
  [∀ y : Y, Invertible (P.coefficients.l : Y.residueField y)]
  (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)
  (S : System P.coefficients.l P.coefficients.Qbar P.field P.coefficients.different (f := f))
  (d : ℕ) [SmoothOfRelativeDimension d f]

end Trace

section BaseChange
open ConstructibleExceptionalCoefficients
variable (P : PurityFiniteSetting.{u}) {X' X Y' Y : Scheme.{u}}
  [X'.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
  [Y'.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
  [QuasiCompact (X' ↘ Spec (.of P.field.k))]
  [IsSeparated (X' ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
  [IsSeparated (Y' ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [∀ x : X', Invertible (P.coefficients.l : X'.residueField x)]
  [∀ x : X, Invertible (P.coefficients.l : X.residueField x)]
  [∀ y : Y', Invertible (P.coefficients.l : Y'.residueField y)]
  [∀ y : Y, Invertible (P.coefficients.l : Y.residueField y)]
  (a : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (b : Y' ⟶ Y)
  [a.IsOver (Spec (.of P.field.k))] [f'.IsOver (Spec (.of P.field.k))]
  [f.IsOver (Spec (.of P.field.k))] [b.IsOver (Spec (.of P.field.k))]
  [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (sq : IsPullback a f' f b) (c' : Compactification f') (c : Compactification f)
  (S' : System P.coefficients.l P.coefficients.Qbar P.field P.coefficients.different (f := f'))
  (S : System P.coefficients.l P.coefficients.Qbar P.field P.coefficients.different (f := f))
  (d : ℕ) [SmoothOfRelativeDimension d f'] [SmoothOfRelativeDimension d f]

/-- Rational smooth exchange: inverse pulled-back purity, the canonical source
comparison, then base-changed purity. This is precisely the defining smooth exchange
of def-pur-smooth-pullback-exchange, transported to rational coefficients.
Source: thm-pur-smooth-base-change-coherence
(blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def rationalSmoothExchange
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) :
    (rationalDerivedPullback P.coefficients.l P.extension a).obj
        ((operation P f c S (.rational (AdicSmoothDualizing.fieldStage P))).G.obj K) ≅
      (operation P f' c' S' (.rational (AdicSmoothDualizing.fieldStage P))).G.obj
        ((rationalDerivedPullback P.coefficients.l P.extension b).obj K) :=
  (rationalDerivedPullback P.coefficients.l P.extension a).mapIso
      (rationalIso P f c S d K).symm ≪≫
    rationalSourceBaseChange P.coefficients.l P.extension a f' f b sq d K ≪≫
    rationalIso P f' c' S' d
      ((rationalDerivedPullback P.coefficients.l P.extension b).obj K)

/-- The same prescribed smooth exchange in the common-stage category.
Source: thm-pur-smooth-base-change-coherence and proof Step 6
(blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def commonSmoothExchange
    (K : generalAlgebraicallyClosedConstructibleCategory
      P.coefficients.l P.coefficients.Qbar Y) :
    (commonStageDerivedPullback P.coefficients.l P.coefficients.Qbar a).obj
        ((operation P f c S .closed).G.obj K) ≅
      (operation P f' c' S' .closed).G.obj
        ((commonStageDerivedPullback P.coefficients.l P.coefficients.Qbar b).obj K) :=
  (commonStageDerivedPullback P.coefficients.l P.coefficients.Qbar a).mapIso
      (commonIso P f c S d K).symm ≪≫
    commonSourceBaseChange P.coefficients.l P.coefficients.Qbar a f' f b sq d K ≪≫
    commonIso P f' c' S' d
      ((commonStageDerivedPullback P.coefficients.l P.coefficients.Qbar b).obj K)

/-- The two paths around every Cartesian square commute, with no restriction on b.
Source: thm-pur-smooth-base-change-coherence, at both field coefficient stages
(blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def BaseChangeClause : Prop :=
  (∀ K : sfRationalConstructibleCategory P.coefficients.l P.extension Y,
    (rationalDerivedPullback P.coefficients.l P.extension a).map
        (rationalIso P f c S d K).hom ≫
        (rationalSmoothExchange P a f' f b sq c' c S' S d K).hom =
      (rationalSourceBaseChange P.coefficients.l P.extension a f' f b sq d K).hom ≫
        (rationalIso P f' c' S' d
          ((rationalDerivedPullback P.coefficients.l P.extension b).obj K)).hom) ∧
  ∀ K : generalAlgebraicallyClosedConstructibleCategory
      P.coefficients.l P.coefficients.Qbar Y,
    (commonStageDerivedPullback P.coefficients.l P.coefficients.Qbar a).map
        (commonIso P f c S d K).hom ≫
        (commonSmoothExchange P a f' f b sq c' c S' S d K).hom =
      (commonSourceBaseChange P.coefficients.l P.coefficients.Qbar a f' f b sq d K).hom ≫
        (commonIso P f' c' S' d
          ((commonStageDerivedPullback P.coefficients.l P.coefficients.Qbar b).obj K)).hom

end BaseChange

open ConstructibleExceptionalCoefficients

end WeilConjectures.RationalPurityCoherence
