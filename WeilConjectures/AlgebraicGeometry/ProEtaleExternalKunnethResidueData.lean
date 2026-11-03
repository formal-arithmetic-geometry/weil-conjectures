/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleExternalKunneth
public import WeilConjectures.AlgebraicGeometry.CoefficientScalarRepresentatives.CoefficientScalarRepresentatives
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.FiniteRingResidueConservativity
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixCtf
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntTensorProjection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleTensorConstructibility
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixFiniteGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixNonfiniteGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixPerfectExtension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientProjectionSquare
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.QlbarDirectImageComparison
import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteScalarProjectionCase
import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarRestrictionMateNormalization
import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarMateProjection
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralFinitePointResolution
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.SixFunctors.ScalarOpenCompositorCoherence
import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenExtensionConstructibleFiniteTor
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientSmallCarrierComparison
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekCompositionModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestrictionMaps
import WeilConjectures.Compactification.BaseChange
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import WeilConjectures.CategoryTheory.CompactGeneratorsBuildObjects
import WeilConjectures.CategoryTheory.CompactObject
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingEtaleCompactGenerators
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupportDerived
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalTowerCoefficients
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimit
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTrace
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1Triangle
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1UnitCounit
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestriction
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenClosedSequenceRingSheaf
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClass
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorHom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCtfSixFunctorStabilityCurrent

/-! # The specified identity-factor map under residue coefficients

Source: sk-lem-sf-kunneth-star, Arbitrary finite coefficient rings
(blueprint: lem-sf-external-kunneth-residue-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.ProEtale
variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- Ctf endpoint bounds and the residue square of the actual
counit-defined identity-factor map.
Source: sk-lem-sf-kunneth-star, Arbitrary finite coefficient rings
(blueprint: lem-sf-external-kunneth-residue-data).

Proof: ctf stability for pullback, tensor and ordinary direct image gives the two
endpoint predicates, including the intermediate Rf_*M predicate.
For A to A/m, ordinary derived scalar extension is the fixed adjoint to restriction;
the finite-discrete/module-object equivalence identifies it with scalar-six change.
Scalar-six preserves the input ctf domains. Its pullback and tensor comparisons,
and its direct-image comparison on ctf inputs, give the two displayed isomorphisms
after forgetting the residue-field action. The scalar/tensor balancing isomorphism
identifies this forgotten extension with tensoring by the constant A/m complex.
Transpose the square by h-star adjoint to Rh-star. Pullback-composition coherence,
the monoidal scalar comparison, and the scalar-six counit equation identify both
transposes with scalar extension of the first counit tensored with identity.
Injectivity of the adjunction Hom equivalence proves the square. This proves an
equality of the specified maps before residue conservativity is applied. No
invertibility of a Künneth map is asserted or assumed here. -/
theorem externalKunnethIdentityMap_residue_data
    (k : Type u) [Field k] (_hk : Finite k ∨ IsAlgClosed k)
    (_hp : (ringChar k).Prime) (l : ℕ) (_hl : l.Prime)
    (_hne : l ≠ ringChar k)
    (_hA : ∃ n : ℕ, 0 < n ∧ ((l ^ n : ℕ) : A) = 0)
    {X Y T : Scheme.{u}} (b : Y ⟶ Spec (.of k)) (c : T ⟶ Spec (.of k))
    (f : X ⟶ Y)
    [LocallyOfFiniteType b] [QuasiCompact b] [IsSeparated b]
    [LocallyOfFiniteType c] [QuasiCompact c] [IsSeparated c]
    [LocallyOfFiniteType (f ≫ b)] [QuasiCompact (f ≫ b)] [IsSeparated (f ≫ b)]
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (Q : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (_hM : exceptionalTransportProEtaleObjects A X M)
    (_hQ : exceptionalTransportProEtaleObjects A T Q) :
    let S := pullback b c
    let K := (upperStar (ModuleCat.{u + 1} A) (pullback.fst b c)).leftDerivedFunctor.obj
        ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj M) ⊗
      (upperStar (ModuleCat.{u + 1} A) (pullback.snd b c)).leftDerivedFunctor.obj Q
    let K' := (lowerStar (ModuleCat.{u + 1} A)
        (pullback.mapOverBaseRight f b c)).rightDerivedFunctor.obj
      ((upperStar (ModuleCat.{u + 1} A) (pullback.fst (f ≫ b) c)).leftDerivedFunctor.obj M ⊗
        (upperStar (ModuleCat.{u + 1} A) (pullback.snd (f ≫ b) c)).leftDerivedFunctor.obj Q)
    let a : K ⟶ K' := externalKunnethIdentityMap A
      ⟨(pullback.mapOverBaseRight_fst f b c).symm⟩
      (pullback.mapOverBaseRight_snd f b c) M Q
    exceptionalTransportProEtaleObjects A Y
      ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj M) ∧
    exceptionalTransportProEtaleObjects A S K ∧
    exceptionalTransportProEtaleObjects A S K' ∧
    ∀ (m : Ideal A) (_hm : m.IsMaximal),
      letI : Finite (A ⧸ m) := Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := m))
      let φ := Ideal.Quotient.mk m
      let ML := (CoefficientScalarRepresentatives.extension
        (Scheme.ProEt.topology X) φ).obj M
      let QL := (CoefficientScalarRepresentatives.extension
        (Scheme.ProEt.topology T) φ).obj Q
      let U := Sheaf.derivedRestrictScalars (Scheme.ProEt.topology S) φ
      let N := (DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)).obj
          (ModuleCat.of A (A ⧸ m)))
      let KL := (upperStar (ModuleCat.{u + 1} (A ⧸ m))
          (pullback.fst b c)).leftDerivedFunctor.obj
            ((lowerStar (ModuleCat.{u + 1} (A ⧸ m)) f).rightDerivedFunctor.obj ML) ⊗
        (upperStar (ModuleCat.{u + 1} (A ⧸ m)) (pullback.snd b c)).leftDerivedFunctor.obj QL
      let KL' := (lowerStar (ModuleCat.{u + 1} (A ⧸ m))
          (pullback.mapOverBaseRight f b c)).rightDerivedFunctor.obj
        ((upperStar (ModuleCat.{u + 1} (A ⧸ m))
            (pullback.fst (f ≫ b) c)).leftDerivedFunctor.obj ML ⊗
          (upperStar (ModuleCat.{u + 1} (A ⧸ m))
            (pullback.snd (f ≫ b) c)).leftDerivedFunctor.obj QL)
      exceptionalTransportProEtaleObjects (A ⧸ m) X ML ∧
      exceptionalTransportProEtaleObjects (A ⧸ m) T QL ∧
      ∃ (e : K ⊗ N ≅ U.obj KL) (e' : K' ⊗ N ≅ U.obj KL'),
        ((derivedTensor (ModuleCat.{u + 1} A) S).map a).app N ≫ e'.hom =
          e.hom ≫ U.map (externalKunnethIdentityMap (A ⧸ m)
            ⟨(pullback.mapOverBaseRight_fst f b c).symm⟩
            (pullback.mapOverBaseRight_snd f b c) ML QL) := by
  sorry

end AlgebraicGeometry.ProEtale
