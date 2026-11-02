/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences
public import WeilConjectures.CategoryTheory.InverseMateEquivalence
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedGeometricPointPerfect
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedPoint.NativeCondensedPointSections
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.WeilObject.Sheaf.Stalk
public import WeilConjectures.ZetaWeil.FrobeniusPointTransportDirect
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
public import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
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
public import WeilConjectures.SixFunctors.ScalarOpenCompositorCoherence
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenExtensionConstructibleFiniteTor
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientSmallCarrierComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekCompositionModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
public import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsRegularEnd

/-! # Native Frobenius transport and coefficient reduction

Source: latest blueprint `def-weil-global-geometric-frobenius`, first arrow in each
cohomology composite and its finite-reduction compatibility clause.
(blueprint: def-weil-frobenius-cohomology-transport).

The canonical transport definitions are moved here from the transport-isomorphism
module, retaining their names and construction data. This module identifies their point
insertion with `directFrobeniusPointTransport` through the common normalized native
pullback comparison, and states their finite-reduction laws.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedFrobeniusTransport

attribute [local instance] IsAlgClosure.isAlgClosed

variable (D : FiniteFieldDatum.{u})

variable (Y₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]

variable (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]

end WeilConjectures.CondensedFrobeniusTransport

attribute [local irreducible] DerivedCategory CategoryTheory.Functor.mapDerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

namespace WeilConjectures
namespace FrobeniusCoefficientReduction

/-- The scalar action already used by `condensedRingCoefficientSections`.
Source: latest blueprint, exact final-object evaluation with scalar restriction.
(blueprint: def-weil-frobenius-cohomology-transport). -/
abbrev sectionAction (B : ScalarSixRing.{u}) (X : Scheme.{u}) :=
  (Mod.regularEndRingHom.op).comp
    ((RingEquiv.toOpposite _).toRingHom.comp (condensedRingScalarSections B.X X))

/-- The regular-module scalar-extension comparison respects the global coefficient action.
Source: latest blueprint, the point scalar comparison in the finite-reduction clause.
(blueprint: def-weil-frobenius-cohomology-transport).

Proof: extension sends the regular B-module to the regular B'-module by multiplication.
The naturality of pulled-back global sections identifies the two scalar actions, and
`extendScalarsObjRegularIso_inv_comp_map` gives the displayed equation. -/
theorem sectionAction_compatible {B B' : ScalarSixRing.{u}} (a : B ⟶ B')
    (X : Scheme.{u}) :
    ∀ b : MonObj.Γ B.X,
      (Mod.extendScalarsObjRegularIso (coefficientMap (Λ := B.X) (Λ' := B'.X) a.hom.hom X)).inv ≫
          (Mod.extendScalars (coefficientMap (Λ := B.X) (Λ' := B'.X) a.hom.hom X)).map
            ((sectionAction B X) b).unop =
        ((sectionAction B' X) (MonObj.Γ.map (R := B.X) (S := B'.X) a.hom.hom b)).unop ≫
          (Mod.extendScalarsObjRegularIso
            (coefficientMap (Λ := B.X) (Λ' := B'.X) a.hom.hom X)).inv := by
  sorry

set_option maxHeartbeats 800000 in
-- Elaborating the native scalar-section comparison requires the full derived interfaces.
/-- The actual balanced section-tensor map `b' ⊗ x ↦ b' · (1 ⊗ x)`.
Its extension-of-regular-module comparison is fixed by multiplication and its unit.
Source: latest blueprint, point scalar comparison; derived pullback composition.
(blueprint: def-weil-frobenius-cohomology-transport). -/
def pointScalarHeart {B B' : ScalarSixRing.{u}} (a : B ⟶ B') (X : Scheme.{u}) :=
  coyonedaSectionsExtendScalarsComparison (MonObj.Γ.map (R := B.X) (S := B'.X) a.hom.hom)
    (sectionAction B X) (sectionAction B' X)
    (Mod.extendScalars (coefficientMap (Λ := B.X) (Λ' := B'.X) a.hom.hom X))
    (Mod.extendScalarsObjRegularIso (coefficientMap (Λ := B.X) (Λ' := B'.X) a.hom.hom X))
    (sectionAction_compatible a X)

/-- The two published point-section presentations have the same canonical scalar action.
This compares functors, so exactness is reused from `NativeCondensedPoint.sections_exact`.
Source: exact final-object evaluation and scalar restriction in
[lem-weil-point-proetale-sections-exact] and [def-weil-ordinary-compact-cohomology].
(blueprint: def-weil-frobenius-cohomology-transport).

Proof: expand both functors as Hom from the regular module followed by restriction of
scalars. The global scalar map is `MonObj.Γ.mapFunctor` of the same point pullback.
Taking its opposite before applying the regular action or taking the opposite of the
resulting action gives the same ring homomorphism, evaluated at every scalar. Thus the
objects and maps of the two module-valued functors agree; the remaining fields are proofs. -/
theorem pointSections_eq_native (D : FiniteFieldDatum.{u}) (B : ScalarSixRing.{u}) :
    condensedRingCoefficientSections B.X (Spec (.of D.k)) =
      NativeCondensedPoint.sections B.X D.k := by
  sorry

attribute [local instance] ModuleCat.extendScalars_preservesKFlatQuasiIso

/-- Scalar extension on the actual point coefficient rings, with ordinary derived tensor.
Source: latest blueprint, `- ⊗ᴸ_B B'` in the reduction display.
(blueprint: def-weil-frobenius-cohomology-transport). -/
abbrev scalar (B B' : ScalarSixRing.{u}) (a : B ⟶ B') :=
  (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (MonObj.Γ.map (R := B.X) (S := B'.X) a.hom.hom)).leftDerivedFunctor

set_option maxHeartbeats 800000 in
-- Elaborating the native scalar-section comparison requires the full derived interfaces.
/-- The point comparison is uniquely determined by its balanced-tensor representative.
The equation is the localization square with the actual left-derived counits, so it
normalizes the comparison on every complex, including K-flat resolutions.
Source: latest blueprint, point scalar comparison and the composition lemma cited there.
(blueprint: def-weil-frobenius-cohomology-transport).

Proof: point sections are exact. On flat-term K-flat resolutions the balanced map above
is the sectionwise tensor identity. Exact evaluation preserves those models and this
identity is invertible at the algebraically closed point. It descends to a natural
isomorphism; the localization universal property and the counit equation give uniqueness.
No coefficient tower or choice of an unspecified isomorphism is used. -/
theorem pointScalar_existsUnique (D : FiniteFieldDatum.{u})
    {B B' : ScalarSixRing.{u}} (a : B ⟶ B') :
    let S := condensedRingCoefficientSections B.X (Spec (.of D.k))
    let S' := condensedRingCoefficientSections B'.X (Spec (.of D.k))
    let E := Mod.extendScalars (coefficientMap (Λ := B.X) (Λ' := B'.X) a.hom.hom (Spec (.of D.k)))
    let T := ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (MonObj.Γ.map (R := B.X) (S := B'.X) a.hom.hom)
    letI : PreservesFiniteLimits S :=
      Eq.mpr (congrArg (fun F ↦ PreservesFiniteLimits F) (pointSections_eq_native D B))
        (NativeCondensedPoint.sections_exact B.X D.k).1
    letI : PreservesFiniteColimits S :=
      Eq.mpr (congrArg (fun F ↦ PreservesFiniteColimits F) (pointSections_eq_native D B))
        (NativeCondensedPoint.sections_exact B.X D.k).2
    letI : PreservesFiniteLimits S' :=
      Eq.mpr (congrArg (fun F ↦ PreservesFiniteLimits F) (pointSections_eq_native D B'))
        (NativeCondensedPoint.sections_exact B'.X D.k).1
    letI : PreservesFiniteColimits S' :=
      Eq.mpr (congrArg (fun F ↦ PreservesFiniteColimits F) (pointSections_eq_native D B'))
        (NativeCondensedPoint.sections_exact B'.X D.k).2
    ∃! e : S.rightDerivedFunctor ⋙ scalar B B' a ≅
        scalarSixChange a (Spec (.of D.k)) ⋙ S'.rightDerivedFunctor,
      ∀ K : HomotopyCategory
          (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of D.k))) Ab.{u + 1})
            (condensedRingObj B.X (Spec (.of D.k)))) (.up ℤ),
        e.hom.app (DerivedCategory.Qh.obj K) ≫
            S'.rightDerivedFunctorIsoMapDerivedCategory.hom.app
              (E.leftDerivedFunctor.obj (DerivedCategory.Qh.obj K)) ≫
            S'.mapDerivedCategory.map (E.leftDerivedFunctorCounit.app K) ≫
            S'.mapDerivedCategoryFactorsh.hom.app ((E.mapHomotopyCategory (.up ℤ)).obj K) =
          T.leftDerivedFunctor.map
              (S.rightDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Qh.obj K)) ≫
            T.leftDerivedFunctor.map (S.mapDerivedCategoryFactorsh.hom.app K) ≫
            T.leftDerivedFunctorCounit.app ((S.mapHomotopyCategory (.up ℤ)).obj K) ≫
            DerivedCategory.Qh.map
              ((NatTrans.mapHomotopyCategory
                (pointScalarHeart a (Spec (.of D.k))) (.up ℤ)).app K) := by
  sorry

set_option maxHeartbeats 800000 in
-- Elaborating the native scalar-section comparison requires the full derived interfaces.
end FrobeniusCoefficientReduction
end WeilConjectures
namespace WeilConjectures

namespace FrobeniusCoefficientReduction

variable (D : FiniteFieldDatum.{u})
variable (Y₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]

end FrobeniusCoefficientReduction
end WeilConjectures
namespace WeilConjectures.FrobeniusCoefficientReduction

open Opposite

/-- The two specified coefficient reductions, normalized on every profinite section.
The endpoint isomorphisms only allow the same named coefficient ring to be bundled
in either equivalent way; the arrow is fixed by the displayed quotient formulas.
Source: node's `A_{E,n} → A_{E,m}` and `O_E → A_{E,m}` clause.
(blueprint: def-weil-frobenius-cohomology-transport). -/
def IsFiniteReduction (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (π : PadicAlgCl.integers ℓ E)
    (n m : ℕ) {B B' : ScalarSixRing.{u}} (a : B ⟶ B') : Prop :=
  (∃ (hmn : m ≤ n) (e : B ≅ (⟨CondensedGeometricPoint.residueRingObj ℓ E π n⟩ : ScalarSixRing.{u}))
      (e' : B' ≅ (⟨CondensedGeometricPoint.residueRingObj ℓ E π m⟩ : ScalarSixRing.{u})),
    ∀ (P : Profinite.{u})
      (s : (CondensedGeometricPoint.residueRingObj ℓ E π n).obj.obj (op P)) (x : P),
      (((e.inv ≫ a ≫ e'.hom).hom.hom.hom.app (op P)) s).down x =
        Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn) (s.down x)) ∨
  (∃ (e : B ≅ (⟨Profinite.padicIntegersRingObj ℓ E⟩ : ScalarSixRing.{u}))
      (e' : B' ≅ (⟨CondensedGeometricPoint.residueRingObj ℓ E π m⟩ : ScalarSixRing.{u})),
    ∀ (P : Profinite.{u})
      (s : (Profinite.padicIntegersRingObj ℓ E).obj.obj (op P)) (x : P),
      (((e.inv ≫ a ≫ e'.hom).hom.hom.hom.app (op P)) s).down x =
        Ideal.Quotient.mk ((Ideal.span ({π} : Set _)) ^ m) (s.down x))

variable (D : FiniteFieldDatum.{u})
variable (Y₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]

end WeilConjectures.FrobeniusCoefficientReduction
