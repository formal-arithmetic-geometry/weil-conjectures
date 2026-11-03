/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

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
public import WeilConjectures.AlgebraicGeometry.ScalarChangeAdjunctions
public import WeilConjectures.AlgebraicGeometry.DerivedScalarRestrictionTensor
public import WeilConjectures.AlgebraicGeometry.CartierDerivedRealization
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import Mathlib.CategoryTheory.EssentialImage
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat

/-! # The specified projective-line direct-image comparison

Source: the final comparison paragraph of sk-prop-geo-p1-adjunction.proof.md,
in literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/sec-the-cycle-class-of-a-divisor-and-the-projective-line/
sk-prop-geo-p1-adjunction/ (blueprint: geo-p1-push-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace AlgebraicGeometry.ProEtale.GeoP1Adjunction
private theorem exactAdjunction_eq (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Adjunction.mapDerivedCategoryRightDerivedAdjunction
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f) =
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).ofNatIsoLeft
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) := by
  refine ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).mapHomotopyCategory
    (.up ℤ)).derived_eq_ofNatIsoLeft
      (HomotopyCategory.quasiIso _ (.up ℤ))
      (HomotopyCategory.quasiIso _ (.up ℤ)) _ _ _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm ?_
  ext M
  simp only [leftDerivedUpperStarIsoMapDerivedCategory, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app]
  rw [← (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctorIsoMapDerivedCategory_hom_fac]
  rw [NatTrans.comp_app, Functor.whiskerLeft_app, Iso.inv_hom_id_app_assoc]

/-- The specified direct-image map is precisely the existing unbounded comparison mate.
Source: comparison transport in sk-prop-geo-p1-adjunction.proof.md
(blueprint: geo-p1-push-comparison).

Proof: the exact inverse-image adjunction is the derived adjunction transported along
its canonical left-derived comparison. The Hom equivalence changes by precomposition
with this comparison. The same compatibility on the ordinary side identifies its
exact counit with the inverse comparison followed by the derived counit. Expanding
the canonical pullback square now gives the same composite on both sides. -/
theorem pushComparison_eq_unbounded (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K : Etale.DerivedCategoryModule A X) :
    geoP1PushComparison A f K = unboundedDirectImageComparisonMap A f K := by
  unfold geoP1PushComparison unboundedDirectImageComparisonMap
  rw [exactAdjunction_eq]
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply]
  apply congrArg ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _)
  have hε :
      (Adjunction.mapDerivedCategoryRightDerivedAdjunction
        (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)).counit.app K =
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).inv.app _ ≫
        (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).counit.app K := by
    have h := congrArg (fun adj ↦ adj.counit.app K)
      (Etale.mapDerivedUpperStarLowerStarAdjunction_eq (ModuleCat.{u + 1} A) f)
    simpa only [Etale.mapDerivedUpperStarLowerStarAdjunction,
      Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
      Functor.whiskerLeft_app] using h
  rw [hε]
  unfold geoP1PullComparison unboundedDirectImagePullbackIso
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc, Iso.symm_hom]
  rfl

/-- Naturality of the actual direct-image comparison composite.
Source: comparison transport in sk-prop-geo-p1-adjunction.proof.md
(blueprint: geo-p1-push-comparison).

Proof: replace both components by their equal unbounded comparison components and
apply the naturality theorem for that comparison. -/
theorem pushComparison_naturality (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) {K L : Etale.DerivedCategoryModule A X} (g : K ⟶ L) :
    (geoP1Comparison A Y).map ((Etale.ordinaryFinitePushforward A f).map g) ≫
      geoP1PushComparison A f L =
    geoP1PushComparison A f K ≫ (geoP1Pushforward A f).map
      ((geoP1Comparison A X).map g) := by
  rw [pushComparison_eq_unbounded, pushComparison_eq_unbounded]
  exact unboundedDirectImageComparisonMap_naturality A f g

/-- The actual direct image preserves the whole classical essential image whenever
its canonical comparison components are invertible.
Source: comparison transport in sk-prop-geo-p1-adjunction.proof.md
(blueprint: geo-p1-push-comparison).

Proof: present a classical object as comparison of an ordinary complex. Apply ordinary
direct image to that complex; its comparison is isomorphic to the required object by
the canonical comparison component and the image of the presentation isomorphism. -/
theorem push_preservesClassical (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ K : Etale.DerivedCategoryModule A X, IsIso (geoP1PushComparison A f K))
    (M : (geoP1Comparison A X).EssImageSubcategory) :
    (geoP1Comparison A Y).essImage ((geoP1Pushforward A f).obj M.obj) := by
  obtain ⟨M₀, ⟨e⟩⟩ := M.property
  have hi : IsIso (geoP1PushComparison A f M₀) := h M₀
  exact ⟨(Etale.ordinaryFinitePushforward A f).obj M₀,
    ⟨asIso (geoP1PushComparison A f M₀) ≪≫ (geoP1Pushforward A f).mapIso e⟩⟩

end AlgebraicGeometry.ProEtale.GeoP1Adjunction
