/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalPurityCoherence.RationalPurityLineComparisons
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

/-! # Rational purity: CommonComparisons

Source: current blueprint, rational purity trace and coherence construction.
Existing declarations are retained in this compilation subdivision.
(blueprint: def-pur-rational-purity-common-comparisons).
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

section Composition
open ConstructibleExceptionalCoefficients
variable (P : PurityFiniteSetting.{u})
  {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [Z.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
  [QuasiCompact (Z ↘ Spec (.of P.field.k))]
  (f : X ⟶ Y) (g : Y ⟶ Z)
  [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
  (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))
  (Sf : System P.coefficients.l P.coefficients.Qbar P.field P.coefficients.different (f := f))
  (Sg : System P.coefficients.l P.coefficients.Qbar P.field P.coefficients.different (f := g))
  (Sfg : System P.coefficients.l P.coefficients.Qbar P.field
    P.coefficients.different (f := f ≫ g))

end Composition

section CommonSources
attribute [local irreducible] commonStageDerivedPullback
attribute [local instance 2000] IntermediateField.algebra'
attribute [local instance 2000] ConstructibleExceptionalCoefficients.category
open AlgebraicallyClosedCoefficients GeneralAlgebraicallyClosedCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Pullback at a literal finite stage, from its published object formula.
Source: proof Step 6 (blueprint: def-pur-rational-purity-common-comparisons). -/
@[irreducible]
def commonPullInclusion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (i : Index l Ω) (K : Stage l Ω Y i) :
    (commonStageDerivedPullback l Ω f).obj ⟨i,K⟩ ≅
      (GeneralAlgebraicallyClosedCoefficients.inclusion i).obj
        ((rationalDerivedPullback l (Coefficient.{u} l Ω i) f).obj K) :=
  by
    unfold commonStageDerivedPullback
    exact eqToIso
      ((commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1 ⟨i, K⟩)

/-- The source comparison around an arbitrary Cartesian square at Qbar, represented
by the rational root/tensor/pullback comparison and the actual stage inclusions.
Source: proof Step 6 (blueprint: def-pur-rational-purity-common-comparisons). -/
@[irreducible]
def commonSourceBaseChange {X' X Y' Y : Scheme.{u}}
    (a : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (b : Y' ⟶ Y)
    [∀ x : X', Invertible (l : X'.residueField x)]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y', Invertible (l : Y'.residueField y)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (sq : IsPullback a f' f b) (d : ℕ)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    (commonStageDerivedPullback l Ω a).obj ((commonSource l Ω f d).obj K) ≅
      (commonSource l Ω f' d).obj ((commonStageDerivedPullback l Ω b).obj K) :=
  (commonStageDerivedPullback l Ω a).mapIso (commonSourceComparison l Ω f d K) ≪≫
    commonPullInclusion l Ω a K.stage _ ≪≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion K.stage).mapIso
      (rationalSourceBaseChange l (Coefficient.{u} l Ω K.stage) a f' f b sq d K.obj) ≪≫
    (commonSourceComparison l Ω f' d
      ⟨K.stage,(rationalDerivedPullback l (Coefficient.{u} l Ω K.stage) b).obj K.obj⟩).symm ≪≫
    (commonSource l Ω f' d).mapIso (commonPullInclusion l Ω b K.stage K.obj).symm

end CommonSources

attribute [local irreducible] commonStageDerivedPullback

section GeometricComposition
attribute [local irreducible] ScalarLocalization.category
attribute [local instance 2000] IntermediateField.algebra'
attribute [local instance 2000] ConstructibleExceptionalCoefficients.category
open ConstructibleExceptionalCoefficients
open AlgebraicallyClosedCoefficients GeneralAlgebraicallyClosedCoefficients
variable (P : PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [Z.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
  [QuasiCompact (Z ↘ Spec (.of P.field.k))]
  [IsSeparated (Z ↘ Spec (.of P.field.k))]
  [∀ x : X, Invertible (P.coefficients.l : X.residueField x)]
  [∀ y : Y, Invertible (P.coefficients.l : Y.residueField y)]
  [∀ z : Z, Invertible (P.coefficients.l : Z.residueField z)]
  (f : X ⟶ Y) (g : Y ⟶ Z)
  [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
  (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))
  (Sf : System P.coefficients.l P.coefficients.Qbar P.field P.coefficients.different (f := f))
  (Sg : System P.coefficients.l P.coefficients.Qbar P.field P.coefficients.different (f := g))
  (Sfg : System P.coefficients.l P.coefficients.Qbar P.field
    P.coefficients.different (f := f ≫ g))

end GeometricComposition

end WeilConjectures.RationalPurityCoherence
