/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.AlgebraicGeometry.LocallyClosedExtensionData.LocallyClosedExtensionCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
public import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportProjectionFormula
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
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
public import Mathlib.Topology.Defs.Filter
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
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarRestrictionMateNormalization
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarMateProjection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralFinitePointResolution
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenExtensionConstructibleFiniteTor
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientSmallCarrierComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekCompositionModel
public import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedMonoidalComparisons
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHomMaps
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportDerivedLocalization
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
public import WeilConjectures.SixFunctors.ScalarOpenCompositorCoherence

/-! # Normalized immersion projection and scalar comparison

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-lem-int-tensor/
det-lem-int-tensor-projection.proof.md, Open immersions, Closed immersions, Derived version
and Locally closed immersions; Stacks Tags 0E8I, 0B56, 0E48, 09BM and 09BN.
(blueprint: lem-sfb-immersion-projection-scalar-normalization).

All tensors are relative, ordinary and uncompleted, and all derived categories are
unbounded. The specified maps are actual adjunction transposes. The separately derived
compactification model is identified with the exact immersion model by the canonical
exact-functor comparison; scalar extension is never assumed flat.

## Main definitions and statements

* `immersionClosedProjection`, `immersionOpenProjection`: the specified adjunction maps.
* `immersionProjection`: their composite with the two symmetries and pullback compositor.
* `immersionOpenScalarMap`, `immersionScalarMap`: the normalized coefficient comparisons.
* `ImmersionClosedScalarSquare`, `ImmersionOpenScalarSquare`,
  `ImmersionProjectionScalarSquare`: the actual commutation equations.
* `immersionProjectionScalarNormalization`: invertibility and scalar compatibility.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Transport the existing normalized support tensor comparison to the recorded upper star.
Source: Stacks 0G7D and the derived paragraph of the source
(blueprint: lem-sfb-immersion-projection-scalar-normalization). -/
def immersionPullTensor (Λ : ScalarSixRing.{u}) {S X : Scheme.{u}} (f : S ⟶ X)
    (C D : DerivedCategory (supportModules Λ.X X)) :
    (scalarSixPull Λ f).obj (C ⊗ D) ≅
      (scalarSixPull Λ f).obj C ⊗ (scalarSixPull Λ f).obj D :=
  (Functor.mapDerivedCategoryNatIso (supportPullbackIsoUpperStar Λ.X f)).symm.app (C ⊗ D) ≪≫
    supportDerivedTensorComparison Λ.X f C D ≪≫
      tensorIso
        ((Functor.mapDerivedCategoryNatIso (supportPullbackIsoUpperStar Λ.X f)).app C)
        ((Functor.mapDerivedCategoryNatIso (supportPullbackIsoUpperStar Λ.X f)).app D)

/-- The specified closed projection is the geometric adjunction transpose of the tensor
comparison followed by counit tensor identity. Direct image is written in its total
right-derived presentation until the exact-functor identification below.
Source: Stacks 0B56, closed-immersion paragraph of the source
(blueprint: lem-sfb-immersion-projection-scalar-normalization). -/
def immersionClosedProjection (Λ : ScalarSixRing.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (B : DerivedCategory (supportModules Λ.X Z))
    (C : DerivedCategory (supportModules Λ.X X)) :
    (RootCoordinateFace.lower Λ.X i).obj B ⊗ C ⟶
      (RootCoordinateFace.lower Λ.X i).obj (B ⊗ (scalarSixPull Λ i).obj C) :=
  (RootCoordinateFace.adjunction Λ.X i).homEquiv _ _
    ((immersionPullTensor Λ i ((RootCoordinateFace.lower Λ.X i).obj B) C).hom ≫
      ((RootCoordinateFace.adjunction Λ.X i).counit.app B ⊗ₘ 𝟙 _))

/-- The specified open tensor map, in ambient-first tensor order, is the open adjunct of
identity tensor the open unit followed by the inverse pullback tensor comparison.
Source: Stacks 0E8I, open-immersion and derived paragraphs of the source
(blueprint: lem-sfb-immersion-projection-scalar-normalization). -/
def immersionOpenProjection (Λ : ScalarSixRing.{u}) {S Z : Scheme.{u}}
    (j : S ⟶ Z) [IsOpenImmersion j]
    (L : DerivedCategory (supportModules Λ.X S))
    (D : DerivedCategory (supportModules Λ.X Z)) :
    (openImmersionLowerShriek Λ.X j).mapDerivedCategory.obj
        ((scalarSixPull Λ j).obj D ⊗ L) ⟶
      D ⊗ (openImmersionLowerShriek Λ.X j).mapDerivedCategory.obj L :=
  ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X j).homEquiv _ _).symm
    ((𝟙 _ ⊗ₘ (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X j).unit.app L) ≫
      (immersionPullTensor Λ j D
        ((openImmersionLowerShriek Λ.X j).mapDerivedCategory.obj L)).inv)

/-- The specified open tensor map is invertible on all unbounded inputs.
Source: Stacks 0E8I and 09BN, open and derived paragraphs
(blueprint: lem-sfb-immersion-projection-scalar-normalization).

Proof: the standing target is Noetherian by finite type over the field, so the open is
quasi-compact and has a complementary closed immersion. Apply
lem-sfb-condensed-support-projection-formula to the published openSupportProjection.
Conjugate by the two Koszul symmetries and supportPullbackIsoUpperStar. The open
Hom bijection identifies the conjugate with the displayed unit adjunct, hence with
immersionOpenProjection. On flat-term K-flat models this is the sheaf map of Tag 0E8I;
exact localization preserves its adjunct by lem-sf-exact-localization-inverse-mate. -/
theorem immersionOpenProjection_isIso (Λ : ScalarSixRing.{u}) (k : Type u) [Field k]
    {S Z : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (j : S ⟶ Z) [IsOpenImmersion j.left]
    (L : DerivedCategory (supportModules Λ.X S.left))
    (D : DerivedCategory (supportModules Λ.X Z.left)) :
    IsIso (immersionOpenProjection Λ j.left L D) := by
  let W : TopologicalSpace.Closeds Z.left :=
    ⟨(Set.range j.left.base)ᶜ, j.left.isOpenEmbedding.isOpen_range.isClosed_compl⟩
  let J := Scheme.IdealSheafData.vanishingIdeal W
  let i := J.subschemeι
  have hij : Set.range i.base = (Set.range j.left.base)ᶜ := by
    change Set.range J.subschemeι = _
    rw [J.range_subschemeι]
    simp [J, W]
  have : IsLocallyNoetherian Z.left :=
    LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have : IsNoetherian Z.left := ⟨⟩
  have : QuasiCompact j.left := inferInstance
  let := closedSupport_lowerStarExact Λ.X i j.left hij
  obtain ⟨_, _, _, hio, _, hd⟩ :=
    condensedSupportDerivedLocalization Λ.X i j.left hij
  apply hd
  · have hsrc := hio ((scalarSixPull Λ j.left).obj D ⊗ L)
    have htgt : IsZero ((supportPullback Λ.X i).mapDerivedCategory.obj
        (D ⊗ (openImmersionLowerShriek Λ.X j.left).mapDerivedCategory.obj L)) := by
      exact ((tensorLeft ((supportPullback Λ.X i).mapDerivedCategory.obj D)).map_isZero
        (hio L)).of_iso (supportDerivedTensorComparison Λ.X i D
          ((openImmersionLowerShriek Λ.X j.left).mapDerivedCategory.obj L))
    exact isIso_of_source_target_iso_zero _ hsrc.isoZero htgt.isoZero
  · apply (NatIso.isIso_map_iff
      (Functor.mapDerivedCategoryNatIso (supportPullbackIsoUpperStar Λ.X j.left)) _).2
    let adj := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X j.left
    have : IsIso adj.unit := Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
    have hh : IsIso (adj.homEquiv _ _ (immersionOpenProjection Λ j.left L D)) := by
      dsimp only [adj, immersionOpenProjection]
      simp only [Equiv.apply_symm_apply]
      infer_instance
    have hcomp : IsIso (adj.unit.app ((scalarSixPull Λ j.left).obj D ⊗ L) ≫
        (upperStar Λ.X j.left).mapDerivedCategory.map
          (immersionOpenProjection Λ j.left L D)) := by
      erw [← adj.homEquiv_unit _ _ (immersionOpenProjection Λ j.left L D)]
      exact hh
    have hi := IsIso.of_isIso_comp_left
      (adj.unit.app ((scalarSixPull Λ j.left).obj D ⊗ L))
      ((upperStar Λ.X j.left).mapDerivedCategory.map (immersionOpenProjection Λ j.left L D))
    exact hi

/-- The supplied open/closed factorization as an actual compactification.
Source: locally closed paragraph of the source
(blueprint: lem-sfb-immersion-projection-scalar-normalization). -/
def immersionCompactification {S Z X : Scheme.{u}} (j : S ⟶ Z) (i : Z ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion i] : Compactification (j ≫ i) where
  Z := Z
  i := j
  g := i
  comm := rfl
  isOpenImmersion := inferInstance
  isProper := inferInstance

end AlgebraicGeometry.ProEtale.CondensedRing
