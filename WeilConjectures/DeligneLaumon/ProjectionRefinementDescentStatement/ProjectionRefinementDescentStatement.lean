/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleCondensedCoefficientFamily
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenProper.CondensedOpenProperPasting
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleDerivedCompositorCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
public import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportProjectionFormula
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.CategoryTheory.SixFunctors.InternalSectionScalarAdjunctionSupplement
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedProjectionAdjunctionNormalization
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarPullbackNormalization
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
import WeilConjectures.PoincareDuality.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.QuotientTensorFlatModel.QuotientTensorLeftFlatComputation
import WeilConjectures.AlgebraicGeometry.QuotientTensorFlatModel.QuotientTensorRightFlatComputation
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientScalarTensorCanonical
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PullIsoMonoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalBraided
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarPullbackSquareCoherence
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarRestrictionMateNormalization
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalPullNormalizationExistence
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleOrigin
public import WeilConjectures.AlgebraicGeometry.Flat.FlatModelGeneration
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleLisseModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleExtensionIso
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLocallyClosedExtension
public import Mathlib.CategoryTheory.Triangulated.Generators
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSheafConeWitness
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralDerivedCoefficientData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralConstantModelLocalResolution
public import WeilConjectures.ProperBaseChange.IntegralLfpLocallyFreeResolution
public import WeilConjectures.ProperBaseChange.CondensedConstructibleSerre
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocallyClosedGeneratorTensorIntersection
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
public import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedExtensionTower
public import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.AlgebraicGeometry.Locally.LocallyPerfectScalarModel
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicConstantLocalModelTor
public import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.AlgebraicGeometry.Sites.QuasiCompact
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseDerivedAux
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientProjectionSquare
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.QlbarDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteScalarProjectionCase
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarMateProjection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralFinitePointResolution
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.ScalarOpenCompositorCoherence
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenExtensionConstructibleFiniteTor
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
public import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientSmallCarrierComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekCompositionModel
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
import Mathlib.Tactic.DefEqTransformations
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.ScalarPullbackMateInverseNormalized
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
public import Mathlib.Topology.Algebra.Ring.Ideal

import all WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
import WeilConjectures.CategoryTheory.ModuleObjects.SixFunctors.ScalarTensorCancellation

/-! # Projection descent and finite quotient reduction

Source: latest blueprint
`literature/blueprint/latest/blueprint/part-duality-trace-formula/`
`sec-poincare-duality/sec-perfect-complexes-on-the-point-and-two-exchange-formulas/`
`sk-thm-sf-tensor-hom/sk-rem-sf-pf-done/fix-prop-projection-formula.md`,
compactification compatibility and finite reduction
(blueprint: lem-sf-projection-refinement-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.CompactificationReindexing
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace WeilConjectures.ProjectionRefinementDescentStatement

/-- The canonical invertible open-adjunction units used by the normalized proper/open map.
The data are the existing derived units and their unique inverses, with no pasting witness.
Source: latest blueprint
`literature/blueprint/latest/blueprint/part-appendices/sec-nagata-compactification/`
`sec-compactifications-and-refinements/sk-def-nagata-sketch-data/`
`sk-prop-sf-pf-coherence/prop-sf-pf-coherence.proof.md`, independence paragraph;
the normalized proper/open map of `lem-zl-condensed-open-proper-pasting`
(blueprint: lem-sf-projection-refinement-descent). -/
def projectionRefinementOpenUnits
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] : CondensedOpenProper.OpenUnits Λ where
  unitIso j := by
    intro hj
    haveI : IsIso (openImmersionLowerShriekUpperStarAdjunction Λ j).unit := inferInstance
    haveI : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit :=
      Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
    exact asIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit
  normalized j := by
    intro hj
    rfl

/-- The normalized proper/open map `Γ_u : j₂! → Ru_* j₁!`, obtained by specializing
`CondensedOpenProper.gamma` to `(j₁, 1_X, u, j₂)` and removing the identity direct image.
Source: latest blueprint
`literature/blueprint/latest/blueprint/part-appendices/sec-nagata-compactification/`
`sec-compactifications-and-refinements/sk-def-nagata-sketch-data/`
`sk-prop-sf-pf-coherence/prop-sf-pf-coherence.proof.md`, independence paragraph;
the normalized proper/open map of `lem-zl-condensed-open-proper-pasting`
(blueprint: lem-sf-projection-refinement-descent). -/
def projectionRefinementGamma
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c₁ c₂ : Compactification f}
    (r : c₁.Refinement c₂) : J Λ c₂.i ⟶ J Λ c₁.i ⋙ R Λ r.hom :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (CondensedOpenProper.rId Λ X).inv (J Λ c₂.i) ≫
    CondensedOpenProper.gamma Λ (projectionRefinementOpenUnits Λ) (CommSq.mk r.i_hom)

/-- The comparison `C_u = c_(p₂,u) ∘ Rp₂*(Γ_u)` of main's statement: whisker the normalized
proper/open map by `Rp₂*`, then apply the canonical direct-image compositor and `u p₂ = p₁`.
Source: latest blueprint
`literature/blueprint/latest/blueprint/part-appendices/sec-nagata-compactification/`
`sec-compactifications-and-refinements/sk-def-nagata-sketch-data/`
`sk-prop-sf-pf-coherence/prop-sf-pf-coherence.proof.md`, independence paragraph;
`lem-sfb-module-derived-compositor-coherence`, canonical direct-image compositor
(blueprint: lem-sf-projection-refinement-descent). -/
def projectionRefinementComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c₁ c₂ : Compactification f}
    (r : c₁.Refinement c₂) : F Λ c₂ ⟶ F Λ c₁ :=
  Functor.whiskerRight (projectionRefinementGamma Λ r) (R Λ c₂.g) ≫
    Functor.whiskerLeft (J Λ c₁.i)
      ((moduleDerivedCompositor Λ r.hom c₂.g).inv ≫
        (eqToIso (congrArg (R Λ) r.hom_g)).hom)

/-- Projection mates descend along arbitrary proper compactification refinements.
Source: latest blueprint
`literature/blueprint/latest/blueprint/part-duality-trace-formula/`
`sec-poincare-duality/sec-perfect-complexes-on-the-point-and-two-exchange-formulas/`
`sk-thm-sf-tensor-hom/sk-rem-sf-pf-done/fix-prop-projection-formula.md`,
compactification compatibility (blueprint: lem-sf-projection-refinement-descent).

Proof: use the etale constructible and Tor comparison, bounded flat constructible models,
flat-constructible tensor stability, truncation triangles and the Serre property to prove
constructibility of the tensor input for finite coefficients, without finite Tor for K.
For higher coefficients, exact constant-model pullback and admissible tensor constructibility
apply, since bounded constructible equals constructible finite Tor. The support restriction
isomorphism defines Γ on all inputs. For finite coefficients the proper/open isomorphism agrees
with Γ by its unit normalization; for higher coefficients use normalized interchange on the
bounded constructible category. Thus C is invertible at K and at the tensor input.
Specialize the proper/open tensor mate to (j₁, j₂, 1_X, u). Projection composition, open tensor
normalization and direct-image compositor naturality give the ambient directed C/pf equation.
Invert C at the two constructible inputs to obtain the θ equation. Identity and vertical
pasting of Γ give the identity and composition laws of C. Cofilteredness supplies common
further refinements and equalizes competing legs; cancellation gives independence, identity
and cocycle of τ, normalized by C. Naturality then descends the projection transformation.
-/
theorem projection_refinement_descent
    (𝔻 : WeilConjectures.FiniteFieldDatum.{u}) (C : 𝔻.CoefficientDatum)
    (Λ : ScalarSixRing.{u})
    (_hΛ : IsAdmissibleCoefficientFor C (Mon.mk Λ.X))
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of 𝔻.k))] [Y.Over (Spec (.of 𝔻.k))]
    [IsSeparated (X ↘ Spec (.of 𝔻.k))] [IsSeparated (Y ↘ Spec (.of 𝔻.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of 𝔻.k))]
    [QuasiCompact (X ↘ Spec (.of 𝔻.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of 𝔻.k))]
    [QuasiCompact (Y ↘ Spec (.of 𝔻.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of 𝔻.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ τ : ∀ c₁ c₂ : Compactification f,
        (boundedConstructible (condensedRingObj Λ.X X)).ι ⋙ F Λ.X c₁ ≅
          (boundedConstructible (condensedRingObj Λ.X X)).ι ⋙ F Λ.X c₂,
      (∀ (c₁ c₂ d : Compactification f) (h₁ : d.Refinement c₁)
          (h₂ : d.Refinement c₂)
          (K : (boundedConstructible (condensedRingObj Λ.X X)).FullSubcategory),
        (τ c₁ c₂).hom.app K ≫ (projectionRefinementComparison Λ.X h₂).app K.obj =
          (projectionRefinementComparison Λ.X h₁).app K.obj) ∧
      (∀ c : Compactification f, τ c c = Iso.refl _) ∧
      (∀ c₁ c₂ c₃ : Compactification f,
        τ c₁ c₂ ≪≫ τ c₂ c₃ = τ c₁ c₃) ∧
      (∀ (c₁ c₂ : Compactification f) (r : c₁.Refinement c₂)
          (K : (boundedConstructible (condensedRingObj Λ.X X)).FullSubcategory),
        IsIso ((projectionRefinementComparison Λ.X r).app K.obj)) ∧
      (∀ (K : (boundedConstructible (condensedRingObj Λ.X X)).FullSubcategory)
          (L : CondensedConstructibleFiniteTor Λ.X Y),
        boundedConstructible (condensedRingObj Λ.X X)
          (K.obj ⊗ (P Λ.X f).obj L.obj)) ∧
      (∀ (c₁ c₂ : Compactification f)
          (K : (boundedConstructible (condensedRingObj Λ.X X)).FullSubcategory)
          (L : CondensedConstructibleFiniteTor Λ.X Y)
          (hT : boundedConstructible (condensedRingObj Λ.X X)
            (K.obj ⊗ (P Λ.X f).obj L.obj)),
        pf Λ.X c₁ K.obj L.obj ≫ (τ c₁ c₂).hom.app ⟨_, hT⟩ =
          ((τ c₁ c₂).hom.app K ⊗ₘ 𝟙 L.obj) ≫ pf Λ.X c₂ K.obj L.obj) ∧
      (∀ (c₁ c₂ : Compactification f) (r : c₁.Refinement c₂)
          (K : D Λ.X X) (L : D Λ.X Y),
        pf Λ.X c₂ K L ≫ (projectionRefinementComparison Λ.X r).app (K ⊗ (P Λ.X f).obj L) =
          ((projectionRefinementComparison Λ.X r).app K ⊗ₘ 𝟙 L) ≫ pf Λ.X c₁ K L) := by
  sorry

/-- The discrete finite quotient map, using the already defined continuous-map ring
construction.
Source: latest blueprint `literature/blueprint/latest/blueprint/part-duality-trace-formula/`
`sec-poincare-duality/sec-perfect-complexes-on-the-point-and-two-exchange-formulas/`
`sk-thm-sf-tensor-hom/sk-rem-sf-pf-done/fix-prop-projection-formula.md`, finite reduction
(blueprint: lem-sf-projection-refinement-descent). -/
def finiteProjectionReductionMap (A : Type) [CommRing A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A] (J : Ideal A) :
    scalarSixTopologicalRing.{u} A ⟶ scalarSixTopologicalRing (A ⧸ J) :=
  scalarSixContinuousMap (Ideal.Quotient.mk J) (continuous_of_discreteTopology)

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard

open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

attribute [local implicit_reducible] moduleObjectDerivedPushforward

set_option maxHeartbeats 400000 in
-- Normalize the canonical scalar comparison and its adjunction-defined maps.
set_option maxHeartbeats 400000 in
-- Normalize the canonical scalar comparison and its adjunction-defined maps.
/-- For finite discrete coefficients the finite constant models and intrinsic finite
presentations define the same bounded constructible objects. -/
private theorem finite_boundedConstructible_iff
    (A : Type) [CommRing A] [Finite A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A]
    (Z : Scheme.{u}) [CompactSpace Z] [QuasiSeparatedSpace Z]
    (M : D (scalarSixTopologicalRing.{u} A).X Z) :
    boundedConstructible (condensedRingObj (scalarSixTopologicalRing A).X Z) M ↔
      constantModelBoundedConstructible (scalarSixTopologicalRing A).X Z M := by
  classical
  obtain ⟨eR, heR⟩ := Profinite.finiteDiscreteCondensedRing_constant.{u} A
  let := heR
  let E := finiteDiscreteCoefficientEquivalence A eR
    (internalToModule (ULift.{u + 1} A)) rfl Z
  have hc (N : ModuleRingedComparison.internalModules (scalarSixTopologicalRing A).X Z) :
      IsConstructibleModuleObject (condensedRingObj (scalarSixTopologicalRing A).X Z) N ↔
        IsConstantModelConstructible (scalarSixTopologicalRing A).X Z N := by
    constructor
    · intro hN
      have h := finiteDiscreteCoefficient_constructible A eR
        (internalToModule (ULift.{u + 1} A)) rfl Z N hN
      have h' := (encoding_constructible_iff A Z eR (E.inverse.obj N)).mp h
      rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩] at h' ⊢
      exact constantConstructible_iso A Z (E.counitIso.app N) h'
    · intro hN
      rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩] at hN
      exact modelStratifiedConstructible _ Z N hN
  exact and_congr Iff.rfl (forall_congr' fun n ↦ hc _)

/-- A bounded flat model remains flat with the same bounds after arbitrary scalar
extension. In particular this retains the interval for a nonflat quotient. -/
private theorem scalar_torAmplitudeIn {Λ Λ' : ScalarSixRing.{u}} (α : Λ ⟶ Λ')
    (Z : Scheme.{u}) (M : D Λ.X Z) (a b : ℤ)
    (hM : _root_.DerivedCategory.torAmplitudeIn
      (ModuleRingedComparison.internalModules Λ.X Z) a b M) :
    _root_.DerivedCategory.torAmplitudeIn
      (ModuleRingedComparison.internalModules Λ'.X Z) a b ((scalarSixChange α Z).obj M) := by
  obtain ⟨P, hge, hle, hf, ⟨e⟩⟩ :=
    (_root_.DerivedCategory.torAmplitudeIn_iff_exists_iso_Q_obj_flat a b M).mp hM
  let := hge
  let := hle
  let φ := coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) α.hom.hom Z
  let E := Mod.extendScalars φ
  let Q : CochainComplex (ModuleRingedComparison.internalModules Λ'.X Z) ℤ :=
    (E.mapHomologicalComplex (.up ℤ)).obj P
  let : E.PreservesFlat := Mod.extendScalars_preservesFlat φ
  have hQflat (n : ℤ) : ObjectProperty.flat (Q.X n) :=
    Functor.PreservesFlat.flat_obj (F := E) (hf n)
  have : Q.IsStrictlyGE a := inferInstance
  have : Q.IsStrictlyLE b := inferInstance
  have hk := CochainComplex.kFlat_of_bounded_of_flat P a b hf
  have := E.isIso_leftDerivedFunctorCounit_app_of_kFlat P hk
  let eQ : (scalarSixChange α Z).obj M ≅ _root_.DerivedCategory.Q.obj Q :=
    E.leftDerivedFunctor.mapIso
      (e.symm ≪≫ ((_root_.DerivedCategory.quotientCompQhIso _).app P).symm) ≪≫
    asIso (E.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj P)) ≪≫
    _root_.DerivedCategory.Qh.mapIso ((E.mapHomotopyCategoryFactors (.up ℤ)).app P) ≪≫
    (_root_.DerivedCategory.quotientCompQhIso _).app Q
  exact (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso eQ.symm
    (_root_.DerivedCategory.torAmplitudeIn_Q_obj_of_flat Q a b hQflat)

end WeilConjectures.ProjectionRefinementDescentStatement
