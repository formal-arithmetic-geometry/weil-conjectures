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

end AlgebraicGeometry.ProEtale.NativeAffineLocalizing
