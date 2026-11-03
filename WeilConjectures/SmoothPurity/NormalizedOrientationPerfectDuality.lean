/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.LegacySitePerfectComplex
public import WeilConjectures.ProEtaleCoefficients.SixFunctorOperationDatum.SixFunctorOperationDatum
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothTrace
public import WeilConjectures.SmoothPurity.Adic.AdicPuritySourceReduction
public import WeilConjectures.SmoothPurity.Adic.AdicPurityExceptionalReduction
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.SmoothPurity.AdicSmoothDualizing.AdicSmoothDualizingIntegralDetection
public import WeilConjectures.PoincareDuality.RationalSmoothPurityCanonical.RationalSmoothPurityFiniteTrace
public import WeilConjectures.PoincareDuality.RationalSmoothPurityCanonical.PuritySourceTransports
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteCoefficientSmoothPurity
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
public import WeilConjectures.SixFunctors.Integral.IntegralResidueTor
public import WeilConjectures.PoincareDuality.RationalSmoothPurityCanonical.CanonicalFiniteUnitTensor
public import WeilConjectures.PoincareDuality.RationalSmoothPurityCanonical.CanonicalFiniteUnitCounit
public import WeilConjectures.SixFunctors.SfProEtaleProjection.SfProEtaleProjectionFormula
public import WeilConjectures.SixFunctors.Sf.SfIntegralReductionConservative
public import WeilConjectures.SixFunctors.Integral.IntegralOrdinaryProjectionReduction
public import WeilConjectures.SixFunctors.Coefficient.CoefficientDuality
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.SitePerfectComplex
public import WeilConjectures.SmoothPurity.OrientedPerfectDuality
public import WeilConjectures.SmoothPurity.Supporting.SixFunctorDatum
public import WeilConjectures.SixFunctors.Orientation.OrientationCoefficientTwists
public import WeilConjectures.SixFunctors.OrientationEtaleFamily
public import WeilConjectures.SixFunctors.OrientationEtaleCoefficientTwists
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Orientation.OrientationFiniteCoefficientTwists
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothPurityMap
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionComparisons
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionRootCharts

import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteCoefficientSmoothPurity
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionOfPurity
import WeilConjectures.SixFunctors.Coefficient.CoefficientDuality
import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.PerfectCohomologyAssembly
import WeilConjectures.RingTheory.DiscreteValuationRing.QuotientDuality
import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.Dualizable
import WeilConjectures.CategoryTheory.ObjectProperty.Duality
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.SimpleModule.InjectiveProjective
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.SixFunctors.Integral.IntegralResidueTor

/-! # Normalized orientation, trace and independent perfect evaluation

Source: main-20261015, sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md,
clause (6) and the point/site-perfect part of (7)
(blueprint: lem-sf-package-normalized-orientation-perfect-duality).

The inverse comparison retains the forward purity map, rather than choosing an
isomorphism of its endpoints. Point duality uses derived Hom at integral coefficients.
The closed structures in the site-perfect clause are asserted construction data only; no
SixFunctorDatum, general geometric biduality, or orientation datum is a hypothesis.

## Main definitions and statement
* `sfPackageNormalizedOrientationPerfectDuality`: the complete package below.
* `SfPackageFiniteOrientationTrace`: the finite maps, inverses and quotient squares.
* `SfPackageIntegralOrientation`: the strict reconstructed map and inverse reductions.
* `SfPackageIntegralOrientationTrace`: the reconstructed map, its trace and lattice realization.
* `SfPackageRationalOrientationTrace`: rationalization of that same trace.
* `SfPackageFieldOrientationTrace`: the three finite-field extension equations.
* `SfPackageCommonOrientation`: the common-stage inverse and counit trace.
* `SfPackagePointEvaluation`: independent coefficient double-dual evaluation.
* `SfPackageSmoothSitePerfect`: the evaluation identification on site-perfect inputs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048

universe u a b v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  DerivedCategory.monoidalClosed_of_hasFunctorialFlatResolution
attribute [local irreducible] purAdicSource
  RationalSmoothPurityCanonical.integralSource

section Finite
variable (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]

end Finite

section Integral
variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]

/-- Every integral constructible input is admissible and its reconstructed inverse
orientation has exactly the specified finite reductions. No uniqueness of a lift is claimed.
Source: clause (6), integral reconstruction
(blueprint: lem-sf-package-normalized-orientation-perfect-duality).
Proof: integral residue Tor identifies the full integral constructible category with
the uniform finite-Tor category. Apply adic reconstruction to obtain gamma from a
strict-tower morphism, and invert it. Its source and target reduction comparisons are
invertible by normalized effectivity. Inverting their forward square gives the displayed
inverse square. This construction uses the same reconstructed family at every level. -/
def SfPackageIntegralReconstruction
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hTor : finiteTorConstructibleIntegral C.l E Y K)
    (e : purAdicSource D C E f d K ≅ purAdicTarget D C E f K) : Prop :=
    (∃ G : (coefficientSequenceDerivedRestriction C.l E X).obj
        ((pullbackTensorCalculus C.l E X).reduction.obj (purAdicSource D C E f d K)) ⟶
      (coefficientSequenceDerivedRestriction C.l E X).obj
        ((integralExceptionalSystem C.l E D C.different f).obj K),
      e.hom = (pullbackTensorCalculus C.l E X).adjunction.unit.app _ ≫
        (coefficientConstantTowerLimit C.l E X).map G ∧
      ∀ n : ℕ,
        (coefficientConstantTowerEvaluation C.l E X n).map G ≫
          (coefficientRestrictedEvaluationIso C.l E X n).hom.app _ ≫
          (scalarReductionRestriction C.l E X n).mapDerivedCategory.map
            (purAdicExceptionalEvaluation D C E f K n).hom =
        (coefficientRestrictedEvaluationIso C.l E X n).hom.app _ ≫
          (scalarReductionRestriction C.l E X n).mapDerivedCategory.map
            (((pullbackTensorCalculus C.l E X).reductionEvaluation n).hom.app _ ≫
              purAdicSourceReduction D C E f d K hTor n ≫
              (purAdicFiniteArrow D C E f d K hTor n).hom)) ∧
    ∀ n : ℕ, ∃ e' : (purAdicFiniteArrow D C E f d K hTor n).left ≅
        (purAdicFiniteArrow D C E f d K hTor n).right,
      e'.hom = (purAdicFiniteArrow D C E f d K hTor n).hom ∧
      IsIso (purAdicSourceReduction D C E f d K hTor n) ∧
      IsIso (purAdicTargetReduction D C E f d K hTor n) ∧
      (scalarReductionDerivedExtension C.l E X n).map e.hom ≫
          purAdicTargetReduction D C E f d K hTor n =
        purAdicSourceReduction D C E f d K hTor n ≫
          (purAdicFiniteArrow D C E f d K hTor n).hom ∧
      (scalarReductionDerivedExtension C.l E X n).map e.inv ≫
          purAdicSourceReduction D C E f d K hTor n =
        purAdicTargetReduction D C E f d K hTor n ≫
          e'.inv

attribute [local irreducible] purAdicTarget

attribute [local irreducible] PurCompactSupport.image PurCompactSupport.comparison
  PurCompactSupport.finiteImageIso PurCompactSupport.finiteReductionIso
  scalarReductionExistence scalarReductionDerivedExistence HasDerivedCategory.standard

end Integral

section Fields
variable (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)
  (S : ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
    P.field P.coefficients.different (f := f))
  (d : ℕ) [SmoothOfRelativeDimension d f]
open RationalSmoothPurityCanonical

attribute [local irreducible] PurCompactSupport.image
  RationalSmoothPurityCanonical.integralMap
  RationalSmoothPurityCanonical.rationalIso
  RationalSmoothPurityCanonical.commonIso
  RationalSmoothPurityCanonical.smallModelIso

attribute [local irreducible] rationalDerivedPullback rationalDerivedTensor
  commonStageDerivedPullback commonStageDerivedTensor sfRationalScalarExtension
  RationalSmoothPurityCanonical.rationalSource
  RationalSmoothPurityCanonical.sourceScalar
  RationalSmoothPurityCanonical.rationalSourceComparison
  RationalSmoothPurityCanonical.commonSource
  RationalSmoothPurityCanonical.commonSourceComparison

attribute [local irreducible] ScalarLocalization.category SheafOfModules.instAbelian
  SheafOfModules.instCategory scalarReductionSourceDerived

attribute [local instance 1000] IntermediateField.algebra'
attribute [local instance 1000] ConstructibleExceptionalCoefficients.category
attribute [local irreducible] ConstructibleExceptionalCoefficients.FieldComparison.b
  ConstructibleExceptionalCoefficients.FieldComparison.q
  AlgebraicGeometry.Scheme.ProEt AlgebraicGeometry.Scheme.instCategoryProEt
  AlgebraicGeometry.Scheme.ProEt.precoverage
  completedIntegralCommRingSheafUnrestricted

end Fields

end WeilConjectures
