/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingCompactificationCoherence
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
public import WeilConjectures.AlgebraicGeometry.CoefficientPullback.FiniteCoefficientPinnedPullbackComparison
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteRootSiteComparison
public import WeilConjectures.AlgebraicGeometry.FiniteNativeTatePullback
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingPullbackFixed
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit

public import WeilConjectures.AlgebraicGeometry.FiniteNativeTensor.FiniteNativeTensorComparison
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceCompactComparisonRestriction
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceRightNormalForm
public import WeilConjectures.AlgebraicGeometry.Geo.GeoP1Cohomology
public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClassDefsSupplement
public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCanonicalChern
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionScalar
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionPullback
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedDefinitions
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.EssImageKernels
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedEquivalence
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalSheaves
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalSheavesModules
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedBelowProEtaleComparison
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.DerivedStalk
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalBounds
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
public import WeilConjectures.CategoryTheory.Sites.InjectivePresheafModuleCechCocycleLiftMax
public import WeilConjectures.CategoryTheory.InjectiveModulePresheaf
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import WeilConjectures.AlgebraicGeometry.EtaleCechVanishingCriterion
public import WeilConjectures.AlgebraicGeometry.EtaleSiteCechComplexComparison
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorUpperBound
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleIntrinsic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekIndependence
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingCompactification
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingConstructibility
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Finiteness
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
public import WeilConjectures.AlgebraicGeometry.UnboundedCoefficientForgetfulAux
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategorySquarePasting
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonSquareProEtalePathNormalization
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonSquareComponent
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalDirectImagePreservation
public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageMateCompatibility
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImageCanonicalMate
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageComparisonMap
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageBoundedBelow
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftComplete
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonDerived
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteClassicalUnboundedComparison
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSupportedDiagonalUnitSupplement
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteDiagonalTraceCoordinates
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ReductionExtendScalars
public import WeilConjectures.CategoryTheory.Cochain.CochainDerivedAdjunction
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.CategoryTheory.Etale.EtaleUnboundedRestrictionComparison
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FiniteCoefficients.Constant
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafCompose
public import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.ProperBaseChange.RingedToposDerivedPushforwardComposition
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.CategoryTheory.ExactDerivedPasting.Word.ExactDerivedTransformationPasting
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.CategoryTheory.K.KInjectiveTotalDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesTwo
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerSystemSupplement
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
public import Mathlib.CategoryTheory.EssentialImage
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDerivedPullbackFixed
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineDiagonalData
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalCartier
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineDiagonalChernComponents
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerMaps
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedCartierKummerSupplement
public import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.GroupTheory.Torsion
public import WeilConjectures.AlgebraicGeometry.ProperUnboundedBaseChangeModN
public import WeilConjectures.AlgebraicGeometry.ProperUnboundedBaseChangeForgetful
public import WeilConjectures.CategoryTheory.Sites.FixedCoefficientDerivedChangeOfRings
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.EtaleCoordinateTraceContractions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import WeilConjectures.AlgebraicGeometry.FiniteAdmissibleComparison
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingTensorTor
public import WeilConjectures.AlgebraicGeometry.GeoP1Adjunction.GeoP1Adjunction
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleOrigin
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkPropSfExistence

/-! # The normalized affine adjunction on the native localizing closure

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/sec-ctf-finite-geometric-restriction/
sk-prop-sf-rf-shriek-preservation/sk-prop-sf-rf-shriek-preservation.proof.md,
affine-projection paragraph, and literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/
sec-the-exceptional-inverse-image-of-a-smooth-morphism-and-base-change/
sk-lem-geo-affine-local/sk-lem-geo-affine-local.proof.md, paragraph (1).
(blueprint: lem-sf-native-affine-localizing-adjunction)

We use the existing ordered affine-line tower as the model of affine space. Its
canonical coordinate isomorphism is `affineTraceAffineSpaceIso`, and its projection
in dimension zero is literally the identity. The native right functor uses the actual
coefficient inverse image, finite root line, ordinary derived tensor and shift.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NativeAffineLocalizing
open FiniteDiscreteOrdinary

variable (A : Type u) [CommRing A] [Finite A]
  [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]

/-- The existing native localizing category, with no completeness condition.
Source: sk-def-localizing-closure (blueprint: lem-sf-native-affine-localizing-adjunction). -/
abbrev Loc (T : Scheme.{u}) := (localizingClosureProEtale (coefficient A) T).FullSubcategory

/-- Actual inverse image, derived tensor with the existing finite Tate power, then shift.
Source: the formula for H in the affine-projection paragraph
(blueprint: lem-sf-native-affine-localizing-adjunction). -/
def right {P Y : Scheme.{u}} (p : P ⟶ Y) (N d : ℕ) :
    DerivedCategory (Internal A Y) ⥤ DerivedCategory (Internal A P) :=
  CoefficientPullback.pull (coefficient A) p ⋙
    (CondensedRing.derivedTensor (coefficient A) P).flip.obj
      ((DerivedCategory.singleFunctor _ 0).obj (finiteNativeTateLine A P N d)) ⋙
    shiftFunctor _ (2 * (d : ℤ))

/-- Restrict H to the full localizing categories using only its membership proof.
Source: the localizing assertion in the node
(blueprint: lem-sf-native-affine-localizing-adjunction). -/
def rightLoc {P Y : Scheme.{u}} (p : P ⟶ Y) (N d : ℕ)
    (h : ∀ K : Loc A Y, localizingClosureProEtale (coefficient A) P
      ((right A p N d).obj K.obj)) : Loc A Y ⥤ Loc A P :=
  (localizingClosureProEtale (coefficient A) P).lift
    ((localizingClosureProEtale (coefficient A) Y).ι ⋙ right A p N d) h

/-- The literal composite of the normalized projective-line/open adjunctions.
Its base case is the identity adjunction; the last coordinate is integrated first.
Source: sk-lem-geo-affine-local.proof.md (1), composite counit formula
(blueprint: lem-sf-native-affine-localizing-adjunction). -/
def ordinaryAdjunction (N : ℕ) (hN : 0 < N)
    (hA : (N : ULift.{u + 1} A) = 0) (Y : Scheme.{u}) [IsNoetherian Y]
    (hY : IsUnit (N : Γ(Y, ⊤))) (d : ℕ) :=
  Etale.affineTraceAdjunction (ULift.{u + 1} A) N hA
    (Etale.projectiveLineTraceTransport N hN (ULift.{u + 1} A) hA)
    (fun T _ hT ↦ Etale.projectiveLineTraceDatum N hN (ULift.{u + 1} A) hA T hT)
    Y hY d

/-- Remove identity scalar restriction from the normalized encoding.
Source: coefficient-identification step of the node's proof
(blueprint: lem-sf-native-affine-localizing-adjunction). -/
def encodingFixed (T : Scheme.{u}) (E : Encoding A T) :
    coefficientEncoding A (Iso.refl _) T E ≅ E.fixedDerived.functor :=
  letI : (E.ordinary.trans E.fixed).functor.Additive :=
    inferInstanceAs (E.ordinary.functor ⋙ E.fixed.functor).Additive
  letI : (E.ordinary.trans E.fixed).inverse.Additive :=
    inferInstanceAs (E.fixed.inverse ⋙ E.ordinary.inverse).Additive
  (CoefficientPullback.pinnedHeartDerivedIso A (coefficient A) (Iso.refl _) T E).symm ≪≫
    Functor.mapDerivedCategoryNatIso (FiniteNativeTensor.heartIdentityIso A T E)

/-- Termwise localization of the canonical open extension-by-zero comparison.
Source: sk-lem-geo-affine-local.proof.md (1), the open counit step
(blueprint: lem-sf-native-affine-localizing-adjunction). -/
def openComparison {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (Etale.openImmersionLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).mapDerivedCategory ⋙
        geoP1Comparison (ULift.{u + 1} A) Z ≅
      geoP1Comparison (ULift.{u + 1} A) X ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (openImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) j) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The specified site comparison on every unbounded input: the proper counit mate,
then the exact open comparison. No inverse mate or unspecified isomorphism is chosen.
Source: finite classical comparison, followed by sk-lem-geo-affine-local.proof.md (1)
(blueprint: lem-sf-native-affine-localizing-adjunction). -/
def siteSupportMap {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : Etale.DerivedCategoryModule (ULift.{u + 1} A) X) :
    (geoP1Comparison (ULift.{u + 1} A) Y).obj
      ((Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) c).obj M) ⟶
    (rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) c).obj
        ((geoP1Comparison (ULift.{u + 1} A) X).obj M) :=
  unboundedDirectImageComparisonMap (ULift.{u + 1} A) c.g
      ((Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) c.i).mapDerivedCategory.obj M) ≫
    (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) c.g).rightDerivedFunctor.map
      ((openComparison A c.i).hom.app M)

/-- The same compact-support map in native coefficients, via the fixed normalized
section-action equivalence. Source: coefficient-identification step of the node's proof
(blueprint: lem-sf-native-affine-localizing-adjunction). -/
def nativeSupportMap (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : Etale.DerivedCategoryModule (ULift.{u + 1} A) X) :
    (internalEtaleRealization A Y (E Y)).obj
      ((Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) c).obj M) ⟶
    (CondensedRing.rightDerivedLowerShriekOfCompactification (coefficient A) c).obj
      ((internalEtaleRealization A X (E X)).obj M) :=
  (E Y).fixedDerived.inverse.map (siteSupportMap A c M) ≫
    (E Y).fixedDerived.inverse.map
      ((rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) c).map
          ((E X).fixedDerived.counitIso.inv.app _)) ≫
    (E Y).fixedDerived.inverse.map ((FiniteNativeTensor.compactEncoding A E c).inv.app _) ≫
    (E Y).fixedDerived.unitIso.inv.app _

/-- The existing canonical normal form of the ordered ordinary right functor.
The factors are the root-induced Tate pullbacks, flat tensor comparisons and even shifts.
Source: sk-lem-geo-affine-local.proof.md (1), twist reassociation
(blueprint: lem-sf-native-affine-localizing-adjunction). -/
def ordinaryNormalForm (N : ℕ) (hN : 0 < N)
    (hA : (N : ULift.{u + 1} A) = 0) (Y : Scheme.{u}) [IsNoetherian Y]
    (hY : IsUnit (N : Γ(Y, ⊤))) (d : ℕ) :=
  Etale.towerENormalForm (ModuleCat.{u + 1} (ULift.{u + 1} A)) N
    (fun X d ↦ Scheme.finiteEtaleTateSheaf (ULift.{u + 1} A) N X hA (d : ℤ))
    (fun f hX d ↦ (Scheme.finiteEtaleTwistPullbackData
      (ULift.{u + 1} A) N hN hA).c f hX (affineTracePullbackInvertible N f hX) d)
    (fun _ ↦ Iso.refl _)
    (fun X hX d ↦ (ObjectProperty.flat_iff_preservesFiniteLimits _).2
      (Scheme.finite_etale_torsion_twist_line X N hN
        (fun x ↦ by
          simpa only [map_natCast] using hX.map (X.presheaf.germ ⊤ x (by trivial)).hom)
        (ULift.{u + 1} A) hA d).2.2.1)
    (fun X hX d ↦
      (Scheme.finiteEtaleTwistPullbackData (ULift.{u + 1} A) N hN hA).p X hX d 1 ≪≫
        eqToIso (congrArg (Scheme.finiteEtaleTateSheaf (ULift.{u + 1} A) N X hA)
          (by omega))) Y hY d

/-- Compare ordered compact support with the actual native compactification functor.
The coordinate support compositor is followed by the same-compactification site mate.
Source: sk-lem-geo-affine-local.proof.md (1), Stacks 0F7J and 0F7K
(blueprint: lem-sf-native-affine-localizing-adjunction). -/
def towerSupportMap (E : ∀ T : Scheme.{u}, Encoding A T)
    (Y : Scheme.{u}) [IsNoetherian Y] (d : ℕ)
    (c : Compactification (affineTraceProjection Y d))
    (M : Etale.DerivedCategoryModule (ULift.{u + 1} A) (affineTraceTower Y d)) :=
  (internalEtaleRealization A Y (E Y)).map
    ((Etale.affineTraceUnboundedCompactComparison (ULift.{u + 1} A) Y d).hom.app M ≫
      (Etale.rightDerivedLowerShriekIso (ULift.{u + 1} A) c).inv.app M) ≫
    nativeSupportMap A E c M

private theorem ordinary_ctf_iff (A : Type u) [CommRing A] [Finite A]
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :
    FiniteDiscreteOrdinary.ordinaryCtf A T K ↔
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (ULift.{u + 1} A)) T K := by
  have hb : FiniteDiscreteOrdinary.ordinaryBoundedConstructible A T K ↔
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (ULift.{u + 1} A)) T K := by
    constructor
    · rintro ⟨hb, hc⟩
      exact DerivedCategory.boundedConstructible_of_boundedConstructibleIntrinsic
        ⟨hb, fun n ↦ (ordinary_constructible_iff A T _).mp (hc n)⟩
    · intro h
      have hi := DerivedCategory.boundedConstructible_le_boundedConstructibleIntrinsic _ h
      exact ⟨hi.1, fun n ↦ (ordinary_constructible_iff A T _).mpr (hi.2 n)⟩
  exact and_congr hb Iff.rfl

private theorem forwardAdjunction
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (eX : C ≌ C') (eY : D ≌ D') (F : C ⥤ D) (F' : C' ⥤ D')
    (cf : F ⋙ eY.functor ≅ eX.functor ⋙ F') (G : D ⥤ C) (adjEt : F ⊣ G) :
    ∃ adjPro : F' ⊣ (eY.inverse ⋙ G ⋙ eX.functor),
      ∀ N, adjPro.counit.app (eY.functor.obj N) =
        F'.map (eX.functor.map (G.map (eY.unitIso.inv.app N))) ≫
          cf.inv.app (G.obj N) ≫ eY.functor.map (adjEt.counit.app N) := by
  classical
  let e := eX
  let ac : (F) ⋙ eY.functor ⊣ eY.inverse ⋙ G :=
    adjEt.comp eY.toAdjunction
  let j : e.inverse ⋙ ((F) ⋙ eY.functor) ≅
      F' :=
    Functor.isoWhiskerLeft e.inverse cf ≪≫
      (Functor.associator e.inverse e.functor (F')).symm ≪≫
      Functor.isoWhiskerRight e.counitIso (F') ≪≫
      Functor.leftUnitor (F')
  let adjPro : F' ⊣
      eY.inverse ⋙ G ⋙ eX.functor :=
    (e.symm.toAdjunction.comp ac).ofNatIsoLeft j
  refine ⟨adjPro, ?_⟩
  · intro N
    rw [Adjunction.ofNatIsoLeft_counit]
    change j.inv.app (eX.functor.obj (G.obj (eY.inverse.obj (eY.functor.obj N)))) ≫
      (e.symm.toAdjunction.comp ac).counit.app (eY.functor.obj N) = _
    rw [Adjunction.comp_counit_app]
    change j.inv.app _ ≫
      ((F) ⋙ eY.functor).map (e.unitIso.inv.app _) ≫
      ac.counit.app (eY.functor.obj N) = _
    dsimp [j]
    simp only [Category.id_comp, Category.assoc]
    change (F').map (e.counitIso.inv.app _) ≫
      cf.inv.app _ ≫ ((F) ⋙ eY.functor).map
        (e.unitIso.inv.app _) ≫ ac.counit.app _ = _
    rw [← cf.inv.naturality_assoc]
    simp only [Functor.comp_map]
    rw [← Functor.map_comp_assoc]
    simp only [e, Equivalence.counitIso_functor_comp, Functor.id_obj]
    rw [(F').map_id, Category.id_comp]
    dsimp [ac]
    rw [Adjunction.comp_counit_app]
    change cf.inv.app _ ≫ eY.functor.map (adjEt.counit.app _) ≫
      eY.counitIso.hom.app (eY.functor.obj N) = _
    rw [eY.counit_app_functor]
    rw [← eY.functor.map_comp]
    have hn := adjEt.counit.naturality (eY.unitIso.inv.app N)
    dsimp only [Functor.id_map, Functor.comp_map] at hn
    erw [← hn]
    rw [eY.functor.map_comp]
    erw [← cf.inv.naturality_assoc]
    rfl

private theorem transportAdjunction
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (eX : C ≌ C') (eY : D ≌ D') (F : C ⥤ D) (F' : C' ⥤ D')
    (cf : F ⋙ eY.functor ≅ eX.functor ⋙ F') (G : D ⥤ C) (G' : D' ⥤ C')
    (cr : eY.functor ⋙ G' ≅ G ⋙ eX.functor) (adjEt : F ⊣ G) :
    ∃ adj : F' ⊣ G', ∀ K,
      cf.hom.app (G.obj K) ≫ F'.map (cr.inv.app K) ≫
        adj.counit.app (eY.functor.obj K) = eY.functor.map (adjEt.counit.app K) := by
  obtain ⟨a, ha⟩ := forwardAdjunction eX eY F F' cf G adjEt
  let j : eY.inverse ⋙ G ⋙ eX.functor ≅ G' :=
    Functor.isoWhiskerLeft eY.inverse cr.symm ≪≫
      Functor.isoWhiskerRight eY.counitIso G' ≪≫ Functor.leftUnitor G'
  refine ⟨a.ofNatIsoRight j, ?_⟩
  intro K
  have hj : cr.inv.app K ≫ j.inv.app (eY.functor.obj K) ≫
      eX.functor.map (G.map (eY.unitIso.inv.app K)) = 𝟙 _ := by
    dsimp only [j, Iso.trans_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.leftUnitor_inv_app, Iso.symm_inv,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv]
    simp only [Category.id_comp, Category.assoc]
    erw [← cr.hom.naturality (eY.unitIso.inv.app K)]
    rw [eY.counitInv_app_functor]
    simp only [Functor.comp_map, ← G'.map_comp_assoc, ← eY.functor.map_comp,
      Iso.hom_inv_id_app, eY.functor.map_id]
    change cr.inv.app K ≫ G'.map (𝟙 (eY.functor.obj K)) ≫ cr.hom.app K = 𝟙 _
    simp
  change cf.hom.app (G.obj K) ≫ F'.map (cr.inv.app K) ≫
    F'.map (j.inv.app (eY.functor.obj K)) ≫ a.counit.app (eY.functor.obj K) = _
  rw [ha]
  calc
    _ = cf.hom.app (G.obj K) ≫
        F'.map (cr.inv.app K ≫ j.inv.app (eY.functor.obj K) ≫
          eX.functor.map (G.map (eY.unitIso.inv.app K))) ≫
        cf.inv.app (G.obj K) ≫ eY.functor.map (adjEt.counit.app K) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = _ := by
      rw [hj]
      simp

private theorem closure_iso {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (S : ObjectProperty C) : (localizingClosure S).IsClosedUnderIsomorphisms := by
  refine ⟨fun e h P hP hS ↦ ?_⟩
  let := hP.2.1
  exact P.prop_of_iso e (h P hP hS)

private theorem encoding_localizing (T : Scheme.{u}) [IsNoetherian T] (E : Encoding A T)
    (K : DerivedCategory (Internal A T)) :
    localizingClosureProEtale (coefficient A) T K ↔
      localizingClosure (DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) T) (E.fixedDerived.functor.obj K) := by
  have hctf (K : DerivedCategory (Internal A T)) :
      (constantModelBoundedConstructible (coefficient A) T K ∧
        _root_.DerivedCategory.finiteTorAmplitude _ K) ↔
      DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) T (E.fixedDerived.functor.obj K) := by
    have ht := (encoding_tensor_tor A T E).2.2
    have hf : _root_.DerivedCategory.finiteTorAmplitude _ K ↔
        _root_.DerivedCategory.finiteTorAmplitude _ (E.fixedDerived.functor.obj K) := by
      constructor
      · rintro ⟨a, b, h⟩
        exact ⟨min a b, b, (ht K _ _ (min_le_right a b)).1
          (h.mono (min_le_left a b) le_rfl)⟩
      · rintro ⟨a, b, h⟩
        exact ⟨min a b, b, (ht K _ _ (min_le_right a b)).2
          (h.mono (min_le_left a b) le_rfl)⟩
    exact (and_congr ((encoding_constructibility A T E).2 K) hf).trans
      (ordinary_ctf_iff A T _)
  let : (E.ordinary.trans E.fixed).functor.Additive :=
    inferInstanceAs (E.ordinary.functor ⋙ E.fixed.functor).Additive
  let : (E.ordinary.trans E.fixed).inverse.Additive :=
    inferInstanceAs (E.fixed.inverse ⋙ E.ordinary.inverse).Additive
  let : E.fixedDerived.functor.IsTriangulated := by
    change (E.ordinary.functor ⋙ E.fixed.functor).mapDerivedCategory.IsTriangulated
    infer_instance
  let : E.fixedDerived.inverse.CommShift ℤ := by
    change (E.fixed.inverse ⋙ E.ordinary.inverse).mapDerivedCategory.CommShift ℤ
    infer_instance
  let : E.fixedDerived.inverse.IsTriangulated := by
    change (E.fixed.inverse ⋙ E.ordinary.inverse).mapDerivedCategory.IsTriangulated
    infer_instance
  exact localizing_equivalence _ _ E.fixedDerived hctf K

private theorem realization_equivalence
    (ell : ℕ) [Fact ell.Prime] (hA : ∃ n : ℕ, (ell : A) ^ n = 0)
    (k : Type u) [Field k] (hk : Finite k ∨ IsAlgClosed k)
    (hell : IsUnit (algebraMap ℤ k (ell : ℤ)))
    (T : Scheme.{u}) [T.Over (Spec (.of k))] [IsNoetherian T]
    [IsSeparated (T ↘ Spec (.of k))] [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))] (E : Encoding A T) :
    ∃ h : ∀ K, localizingClosureProEtale (coefficient A) T
      ((internalEtaleRealization A T E).obj K),
      ((localizingClosureProEtale (coefficient A) T).lift
        (internalEtaleRealization A T E) h).IsEquivalence := by
  classical
  let Q := localizingClosure (DerivedCategory.constructibleFiniteTor
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) T)
  let := closure_iso (DerivedCategory.constructibleFiniteTor
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) T)
  let el := E.fixedDerived.congrFullSubcategory (show
      Q.inverseImage E.fixedDerived.functor = localizingClosureProEtale (coefficient A) T by
    funext K
    exact propext (encoding_localizing A T E K).symm)
  obtain ⟨l, ⟨hl⟩⟩ := (finiteAdmissibleComparison.{u, u + 1} k hk ell hell A hA T).2.1
  let e := l.trans el.symm
  let norm : e.functor ⋙ (localizingClosureProEtale (coefficient A) T).ι ≅
      internalEtaleRealization A T E :=
    Functor.isoWhiskerRight hl E.fixedDerived.inverse
  have h (K) : localizingClosureProEtale (coefficient A) T
      ((internalEtaleRealization A T E).obj K) := by
    let : (localizingClosureProEtale (coefficient A) T).IsClosedUnderIsomorphisms :=
      closure_iso _
    exact (localizingClosureProEtale (coefficient A) T).prop_of_iso
      (norm.app K) (e.functor.obj K).property
  let H := (localizingClosureProEtale (coefficient A) T).lift
    (internalEtaleRealization A T E) h
  let i : e.functor ≅ H :=
    ((localizingClosureProEtale (coefficient A) T).fullyFaithfulι.whiskeringRight _).preimageIso
      norm
  exact ⟨h, Functor.isEquivalence_of_iso i⟩

private theorem tower_support_iso
    (ell : ℕ) [Fact ell.Prime] (hA : ∃ n : ℕ, (ell : ULift.{u + 1} A) ^ n = 0)
    (k : Type u) [Field k] (hk : Finite k ∨ IsAlgClosed k)
    (hell : IsUnit (algebraMap ℤ k (ell : ℤ)))
    (Y : GeoP1Adjunction.Base k) (d : ℕ)
    (E : ∀ T : Scheme.{u}, Encoding A T)
    (c : Compactification (affineTraceProjection Y.scheme d)) :
    ∃ e : Etale.affineTraceLeft (ULift.{u + 1} A) Y.scheme d ⋙
        internalEtaleRealization A Y.scheme (E Y.scheme) ≅
      internalEtaleRealization A (affineTraceTower Y.scheme d) (E _) ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification (coefficient A) c,
      ∀ M, e.hom.app M = towerSupportMap A E Y.scheme d c M := by
  let C := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let : Y.scheme.Over (Spec (.of k)) := ⟨Y.structureMap⟩
  let : IsSeparated (Y.scheme ↘ Spec (.of k)) := Y.separated
  let : LocallyOfFiniteType (Y.scheme ↘ Spec (.of k)) := Y.locallyOfFiniteType
  let : QuasiCompact (Y.scheme ↘ Spec (.of k)) := Y.quasiCompact
  let : c.Z.Over (Spec (.of k)) := ⟨c.g ≫ Y.structureMap⟩
  let : LocallyOfFiniteType (c.Z ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (c.g ≫ Y.structureMap))
  let : QuasiCompact (c.Z ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (c.g ≫ Y.structureMap))
  have hi (K : Etale.DerivedCategoryModule (ULift.{u + 1} A) c.Z) :
      IsIso (unboundedDirectImageComparisonMap (ULift.{u + 1} A) c.g K) :=
    unboundedDirectImageComparison k hk hell (ULift.{u + 1} A) hA c.g K
  let dir : (Etale.lowerStar C c.g).rightDerivedFunctor ⋙ geoP1Comparison _ Y.scheme ≅
      geoP1Comparison _ c.Z ⋙ (lowerStar C c.g).rightDerivedFunctor :=
    NatIso.ofComponents (fun K ↦ asIso (unboundedDirectImageComparisonMap _ c.g K))
      (fun f ↦ unboundedDirectImageComparisonMap_naturality _ c.g f)
  let site : Etale.rightDerivedLowerShriekOfCompactification C c ⋙
        geoP1Comparison _ Y.scheme ≅
      geoP1Comparison _ (affineTraceTower Y.scheme d) ⋙
        rightDerivedLowerShriekOfCompactification C c :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ dir ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (openComparison A c.i) _ ≪≫ Functor.associator _ _ _
  have hs (M) : site.hom.app M = siteSupportMap A c M := by
    simp only [site, dir, siteSupportMap, Iso.trans_hom, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Iso.symm_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      NatIso.ofComponents_hom_app, asIso_hom, Category.id_comp, Category.comp_id]
    rfl
  let X := affineTraceTower Y.scheme d
  let RX := internalEtaleRealization A X (E X)
  let NY := (E Y.scheme).fixedDerived
  let native : Etale.rightDerivedLowerShriekOfCompactification C c ⋙
        internalEtaleRealization A Y.scheme (E Y.scheme) ≅
      RX ⋙ CondensedRing.rightDerivedLowerShriekOfCompactification (coefficient A) c :=
    Functor.isoWhiskerRight site NY.inverse ≪≫
      Functor.isoWhiskerLeft (geoP1Comparison _ X)
        (Functor.isoWhiskerRight (E X).fixedDerived.counitIso.symm
          (rightDerivedLowerShriekOfCompactification C c ⋙ NY.inverse)) ≪≫
      Functor.isoWhiskerLeft RX
        (Functor.isoWhiskerRight (FiniteNativeTensor.compactEncoding A E c).symm NY.inverse) ≪≫
      Functor.isoWhiskerLeft
        (RX ⋙ CondensedRing.rightDerivedLowerShriekOfCompactification (coefficient A) c)
        NY.unitIso.symm
  have hn (M) : native.hom.app M = nativeSupportMap A E c M := by
    simp only [native, nativeSupportMap, Iso.trans_hom, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom, hs,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.comp_map]
    rfl
  let ord : Etale.affineTraceLeft (ULift.{u + 1} A) Y.scheme d ≅
      Etale.rightDerivedLowerShriekOfCompactification C c :=
    Etale.affineTraceUnboundedCompactComparison _ Y.scheme d ≪≫
      (Etale.rightDerivedLowerShriekIso (ULift.{u + 1} A) c).symm
  refine ⟨Functor.isoWhiskerRight ord _ ≪≫ native, ?_⟩
  intro M
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.whiskerRight_app, hn,
    ord, towerSupportMap, Iso.symm_hom, Functor.isoWhiskerRight_hom]

private theorem whiskerLeft_app_iso
    {C : Type*} {D : Type*} {E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) {G H : D ⥤ E} (e : G ≅ H) (X : C) :
    (Functor.isoWhiskerLeft F e).app X = e.app (F.obj X) := rfl

private theorem whiskerRight_app_iso
    {C : Type*} {D : Type*} {E : Type*} [Category* C] [Category* D] [Category* E]
    {F G : C ⥤ D} (e : F ≅ G) (H : D ⥤ E) (X : C) :
    (Functor.isoWhiskerRight e H).app X = H.mapIso (e.app X) := rfl

private theorem symm_app_iso
    {C : Type*} {D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (e : F ≅ G) (X : C) :
    e.symm.app X = (e.app X).symm := rfl

private theorem flipIso_app
    {C : Type*} {D : Type*} {E : Type*} [Category* C] [Category* D] [Category* E]
    {F G : C ⥤ D ⥤ E} (e : F ≅ G) (Y : D) (X : C) :
    (((flipFunctor _ _ _).mapIso e).app Y).app X = (e.app X).app Y := rfl

private theorem flipMapIso_app
    {C : Type*} {D : Type*} {E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D ⥤ E) {Y Z : D} (e : Y ≅ Z) (X : C) :
    (F.flip.mapIso e).app X = (F.obj X).mapIso e := rfl

private theorem flipObj_mapIso
    {C : Type*} {D : Type*} {E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D ⥤ E) {X Y : C} (e : X ≅ Y) (Z : D) :
    (F.flip.obj Z).mapIso e = (F.mapIso e).app Z := rfl

private theorem comp_mapIso
    {C : Type*} {D : Type*} {E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (G : D ⥤ E) {X Y : C} (e : X ≅ Y) :
    (F ⋙ G).mapIso e = G.mapIso (F.mapIso e) := rfl

private theorem associator_app_iso
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    (a : C ⥤ D) (b : D ⥤ E) (c : E ⥤ F) (K : C) :
    (Functor.associator a b c).app K = Iso.refl _ := rfl

private theorem rightUnitor_app_iso
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) (K : C) :
    F.rightUnitor.app K = Iso.refl _ := rfl

private theorem bifunctor_comparison_app
    {E O : Type*} [Category* E] [Category* O]
    (V W : E ⥤ O) (l : W ≅ V) (Te : E ⥤ E ⥤ E) (To : O ⥤ O ⥤ O)
    (t : Te ⋙ (Functor.whiskeringRight _ _ _).obj W ≅
      (((Functor.whiskeringLeft₂ O).obj W).obj W).obj To) (X : E) :
    (((Functor.postcompose₂.mapIso l.symm).app Te ≪≫ t ≪≫
      ((((Functor.whiskeringLeft₂ O).obj W).mapIso l).app To) ≪≫
      (((Functor.whiskeringLeft₂ O).mapIso l).app V).app To).app X) =
      Functor.isoWhiskerLeft (Te.obj X) l.symm ≪≫ t.app X ≪≫
        Functor.isoWhiskerRight l (To.obj (W.obj X)) ≪≫
        Functor.isoWhiskerLeft V (To.mapIso (l.app X)) := by
  apply Iso.ext
  apply NatTrans.ext
  funext Y
  rfl

private theorem comparison_app
    {J : Type*} {N : Type*} {O : Type*} {E : Type*}
    [Category* J] [Category* N] [Category* O] [Category* E]
    (M : J ⥤ N) (I : J ⥤ O) (U : J ⥤ E) (V : E ⥤ O) (F : N ⥤ O)
    (Tn : N ⥤ N ⥤ N) (To : O ⥤ O ⥤ O) (Te : E ⥤ E ⥤ E)
    (Sn : N ⥤ N) (So : O ⥤ O) (Se : E ⥤ E)
    (Ln : N) (Lo : O) (Le : E)
    (a : Sn ⋙ F ≅ F ⋙ So)
    (b : Tn.flip.obj Ln ⋙ F ≅ F ⋙ To.flip.obj (F.obj Ln))
    (c : M ⋙ F ≅ I) (l : F.obj Ln ≅ Lo) (p : I ≅ U ⋙ V)
    (q : V.obj Le ≅ Lo) (t : Te.flip.obj Le ⋙ V ≅ V ⋙ To.flip.obj (V.obj Le))
    (s : Se ⋙ V ≅ V ⋙ So) (K : J) :
    (((Functor.isoWhiskerLeft (M ⋙ Tn.flip.obj Ln) a ≪≫
        Functor.isoWhiskerRight (Functor.isoWhiskerLeft M b) So ≪≫
        Functor.isoWhiskerRight c (To.flip.obj (F.obj Ln) ⋙ So) ≪≫
        Functor.isoWhiskerLeft I (Functor.isoWhiskerRight (To.flip.mapIso l) So) ≪≫
        Functor.isoWhiskerRight p (To.flip.obj Lo ⋙ So)) ≪≫
      (Functor.isoWhiskerLeft (U ⋙ V)
          (Functor.isoWhiskerRight (To.flip.mapIso q.symm) So) ≪≫
        Functor.isoWhiskerRight (Functor.isoWhiskerLeft U t.symm) So ≪≫
        Functor.isoWhiskerLeft (U ⋙ Te.flip.obj Le) s.symm)).app K) =
      (a.app ((Tn.obj (M.obj K)).obj Ln) ≪≫
        So.mapIso (b.app (M.obj K) ≪≫
          (To.mapIso (c.app K)).app (F.obj Ln) ≪≫ (To.obj (I.obj K)).mapIso l)) ≪≫
        So.mapIso ((To.mapIso (p.app K)).app Lo ≪≫
          (To.obj (V.obj (U.obj K))).mapIso q.symm ≪≫ (t.app (U.obj K)).symm) ≪≫
        s.symm.app ((Te.obj (U.obj K)).obj Le) := by
  apply Iso.ext
  simp only [Iso.app_hom, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.map_comp, Category.assoc]
  rfl

end AlgebraicGeometry.ProEtale.NativeAffineLocalizing
