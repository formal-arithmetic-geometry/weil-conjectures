/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.TraceFormulaCoefficientConventions.TraceFormulaCoefficientConventions
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalDualizingObject
public import WeilConjectures.SmoothPurity.AdicSmoothDualizing.AdicSmoothDualizingIntegralDetection
public import WeilConjectures.AlgebraicGeometry.Picard.TraceFormulaCoefficientConventions.TraceFormulaLocalFrobeniusOperator
public import WeilConjectures.SixFunctors.Coefficient.CoefficientDuality
public import WeilConjectures.SixFunctors.Integral.IntegralConstructibleInternalHom
public import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteExceptionalInverseImage
public import WeilConjectures.SixFunctors.Supporting.GeometricCommonStageDirectImage
public import WeilConjectures.SixFunctors.FrobeniusExchange.SystemOperationExchangeRealization
public import WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization
public import WeilConjectures.SmoothPurity.Exceptional.ExceptionalAdjointAdmissibility
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionComparisons
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.DeligneLaumon.SfWeilSheafComplex
public import WeilConjectures.SmoothPurity.FrobeniusCoefficientTwists.FrobeniusCoefficientTwistsCanonical
public import WeilConjectures.DeligneLaumon.FrobeniusCohomologyTransportIso
public import WeilConjectures.SixFunctors.CommonStageCompactWeilCohomology
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.SixFunctors.FrobeniusCohomologyTransport
public import WeilConjectures.SmoothPurity.Adic.AdicPurityRootComparisons
public import WeilConjectures.PoincareDuality.Point.PointSectionsDerivedReduction
public import WeilConjectures.TraceFormula.Supporting.PointSectionsFiniteReductionData
public import WeilConjectures.TraceFormula.Supporting.PointFiniteReductionSectionAlgebra
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.Picard.DerivedTensorSecondFactorFunctor
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.CochainComplexMinus
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExact
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.Picard.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree
public import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPoint
public import WeilConjectures.SixFunctors.FrobeniusExchange.FrobeniusGeometricExchange
public import WeilConjectures.ZetaWeil.FrobeniusPointTransport
public import WeilConjectures.SmoothPurity.Point.PointSectionsScalarExtension
public import WeilConjectures.SixFunctors.Isomorphism.IsomorphismComparisonScalarExtension
public import WeilConjectures.SixFunctors.Integral.IntegralReductionTowerWellDefinedUnrestricted
public import WeilConjectures.Algebra.Homology.FlatSingleDerivedNormalization.FlatSingleDerivedNormalization
public import WeilConjectures.SmoothPurity.Supporting.SignedTwistFirstReduction
public import WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteSmoothPullbackExchange
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SchemeGeometricFrobenius
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.ZetaWeil.OrdinaryCompactCohomology

/-! # Poincare duality conventions

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
`sk-cor-sp-all-coefficients/def-pod-conventions.md`
(blueprint: def-pod-conventions).

The structure records the global finite-field, coefficient, smooth geometric and
exceptional-adjoint data used by the Poincare-duality statements.  Its projections
reuse the recorded categories, operations, Frobenius and geometric-fibre constructions.

## Main definitions
* `PoincareDualityConventions`: the fixed field, coefficients and geometric hypotheses.
* `PoincareDualityConventions.coefficientOperation`: the recorded exceptional adjunctions.
* `PoincareDualityConventions.finiteOrientation` and the three higher orientations.
* `PoincareDualityConventions.pointDual` and the four coefficient and Verdier duals.
* The four ordinary/compact cohomology and Frobenius conventions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
  AlgebraicGeometry.Scheme Opposite

namespace WeilConjectures

/-- The exact finite-stage exceptional-adjoint predicate for the structure morphism.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
`sk-cor-sp-all-coefficients/def-pod-conventions.md`
(blueprint: def-pod-conventions). -/
noncomputable def poincareExceptionalAdmissibility
    (B : TraceFormulaCoefficientConventions.{u}) (n : ℕ) (hn : 1 ≤ n) : Prop := by
  let S : Scheme := Spec (CommRingCat.of B.datum.k)
  let X := B.geometricBaseChange
  letI : X.Over S := ⟨B.structureMap⟩
  let f : X ⟶ S := X ↘ S
  letI : S.Over S := ⟨𝟙 S⟩
  letI : LocallyOfFiniteType (X ↘ S) := B.geometricFiniteType
  letI : QuasiCompact (X ↘ S) := B.geometricQuasiCompact
  letI : IsSeparated (X ↘ S) := B.geometricSeparated
  let hS : ∀ t : S, IsUnit (B.coefficients.l : S.presheaf.stalk t) := by
    intro t
    let φ : B.datum.k →+* S.presheaf.stalk t :=
      (S.presheaf.germ ⊤ t trivial).hom.comp
        (Scheme.ΓSpecIso (.of B.datum.k)).inv.hom
    simpa only [map_natCast] using (finiteFieldDatumPrimeUnit B.datum
      B.coefficients.l B.coefficients.different).map φ
  letI := hasCompactification_of_finiteType_over_field B.datum.k X S f
  exact IsExceptionalAdjointAdmissibleAtFiniteStage B.coefficients.l B.extension.val n hn
    S X S hS f (HasCompactification.compactification f)

/-- The Poincare-duality convention package.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
`sk-cor-sp-all-coefficients/def-pod-conventions.md`
(blueprint: def-pod-conventions).

The fields fix the finite field datum, a finite coefficient extension and positive
level, a smooth separated geometrically connected finite-type model of pure dimension
`d`, and exceptional-adjoint admissibility at every finite coefficient stage.  The
inherited fields provide the coefficient ring, geometric base change and the finite
constructible derived pullback, tensor and internal-Hom operations.
-/
structure PoincareDualityConventions where
  datum : FiniteFieldDatum.{u}
  coefficients : datum.CoefficientDatum
  extension : Padic.FiniteCoefficientFields coefficients.l coefficients.Qbar
  level : ℕ
  level_pos : 1 ≤ level
  X₀ : Over (Spec (CommRingCat.of datum.k₀))
  [finite_type : LocallyOfFiniteType X₀.hom]
  [quasi_compact : QuasiCompact X₀.hom]
  [separated : IsSeparated X₀.hom]
  d : ℕ
  [smooth : SmoothOfRelativeDimension d X₀.hom]
  [geometrically_connected : GeometricallyConnected X₀.hom]
  exceptional_adjoint_admissible : ∀ (n : ℕ) (hn : 1 ≤ n),
    poincareExceptionalAdmissibility
      ⟨datum, coefficients, extension, level, level_pos, X₀⟩ n hn

attribute [instance] PoincareDualityConventions.smooth
  PoincareDualityConventions.geometrically_connected
  PoincareDualityConventions.finite_type PoincareDualityConventions.quasi_compact
  PoincareDualityConventions.separated

namespace PoincareDualityConventions

/-- Trace-formula coordinates constructed from the independently fixed setting fields.
Source: finite-field and coefficient conventions [def-weil-finite-field-fiber], and
[def-weil-geometric-hypotheses] (blueprint: def-pod-conventions). -/
noncomputable abbrev base (P : PoincareDualityConventions.{u}) :
    TraceFormulaCoefficientConventions.{u} :=
  ⟨P.datum, P.coefficients, P.extension, P.level, P.level_pos, P.X₀⟩

/-- The fixed geometric fibre `X = X₀ × k`.
Source: [def-weil-finite-field-fiber] (blueprint: def-pod-conventions). -/
noncomputable abbrev X (P : PoincareDualityConventions.{u}) : Scheme.{u} :=
  P.base.geometricBaseChange

/-- The geometric point `s = Spec k`.
Source: [def-weil-finite-field-fiber] (blueprint: def-pod-conventions). -/
noncomputable abbrev s (P : PoincareDualityConventions.{u}) : Scheme.{u} :=
  Spec (CommRingCat.of P.base.datum.k)

/-- The structure morphism `a_X : X → s`.
Source: [def-weil-finite-field-fiber] (blueprint: def-pod-conventions). -/
noncomputable abbrev structureMap (P : PoincareDualityConventions.{u}) :
    P.X ⟶ P.s := P.base.structureMap

/-- Finite type survives the geometric base change.
Source: [def-weil-geometric-hypotheses] (blueprint: def-pod-conventions). -/
instance geometricFiniteType (P : PoincareDualityConventions.{u}) :
    LocallyOfFiniteType (P.X ↘ P.s) := P.base.geometricFiniteType

/-- Quasi-compactness survives the geometric base change.
Source: [def-weil-geometric-hypotheses] (blueprint: def-pod-conventions). -/
instance geometricQuasiCompact (P : PoincareDualityConventions.{u}) :
    QuasiCompact (P.X ↘ P.s) := P.base.geometricQuasiCompact

/-- Separatedness survives the geometric base change.
Source: [def-weil-geometric-hypotheses] (blueprint: def-pod-conventions). -/
instance geometricSeparated (P : PoincareDualityConventions.{u}) :
    IsSeparated (P.X ↘ P.s) := P.base.geometricSeparated

/-! The six operations used below are aliases for the recorded constructions.  In
particular, the finite exceptional inverse image uses the recorded etale-origin
construction at the chosen compactification. -/

end PoincareDualityConventions
end WeilConjectures
