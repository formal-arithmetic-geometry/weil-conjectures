/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleUnboundedRestrictionComparison
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
public import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsSupplement
public import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import WeilConjectures.CategoryTheory.RingedToposRingData
public import WeilConjectures.CategoryTheory.AdjunctionRingOperations
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.GeometricModuleTransport
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.GeometricRingTransport
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
public import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
public import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
public import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIsoSupplement
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

public import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.CategoryTheory.ExactDerivedTransformationPasting
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.ExactFunctorDerivedFunctor
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.CategoryTheory.KInjectiveTotalDerived
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsMixedUniverses

/-! # Unbounded étale coefficient restriction and geometric adjuncts

Source: Stacks Project, sites-cohomology.tex, Tag 0FPI,
lemma-adjoints-push-pull-compatibility, with the coefficient-restriction deduction
and the K-injective composition normalization of Tag 0D6E
(blueprint: lem-sf-etale-unbounded-restriction-adjunct).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- Exact coefficient restriction preserves geometric transposes on the full unbounded
étale derived categories. The inverse-image comparison is the existing exact-derived
`scalarRestrictionPullbackIso`; the isomorphism `v` is required both to equal its mate
and to have the specified K-injective direct-image composition normalization.

Source: Stacks Project, sites-cohomology.tex, Tags 07A6, 0D6E and 0FPI,
lemma-adjoints-push-pull-compatibility; the coefficient-restriction deduction recorded
in the DAG (blueprint: lem-sf-etale-unbounded-restriction-adjunct).

Write UY, UZ, gB and gR for the ordinary restriction and direct-image functors.
The equation quantified over I and J spells out the resolution identifications: its
left side identifies UY(Q(gB I)) with UY(GB(QI)) and then applies v. Its right side
uses the sectionwise identity UY gB = gR UZ, applies Q(gR j), and identifies the result
with GR(UZ(QI)) using the right-derived unit at J and the inverse of Qj. Thus this
is the normalized comparison of the two ringed-topos factorizations, not an arbitrary
isomorphism with the same endpoints. The homotopy-category formulation uses every
chain-level K-injective resolution and imposes no K-injectivity on UZ I.

Proof:
1. On sheaves the two inverse images have the same underlying abelian inverse image.
Restriction changes only the scalar action, and the identity is linear because a scalar
r acts through φ(r) on either side. This is the canonical sheaf comparison whose exact
derived descent is scalarRestrictionPullbackIso. Direct images commute with restriction
sectionwise, giving lowerStarRestrictScalarsIso. The ordinary adjunction units are
the abelian units, so transposing a restricted map agrees with restricting its transpose.
The termwise adjunction passes to homotopy categories.
2. All inverse images and restrictions are exact. Their termwise descents and the
localized sheaf comparison therefore give the specified unbounded inverse-image square.
Exact restriction also agrees with its right derived functor on every complex.
3. Represent the target by a K-injective B-complex I, and resolve UZ I by a K-injective
R-complex J via j. Direct image preserves K-injectives because inverse image is exact;
this is used for gB I and gR J only, never for UZ I or UY(gB I).
4. Compare the two ringed-topos factorizations. For gB followed by UY, the intermediate
resolution can be the identity on gB I. For UZ followed by gR, use j. The composition
normalization says gR j is a quasi-isomorphism and gives precisely the displayed
representative equation for v. This fixes the natural isomorphism on every object.
5. Represent t by a chain map h into I. Its B-transpose is gB(h) composed with the
ordinary unit. The R-transpose of j composed with UZ(h) and the inverse-image comparison
is gR(j) composed with UY of that B-transpose, by the ordinary unit identity in step 1.
Localizing identifies this with UY(t sharp) followed by v. Hence v is the existing
geometric mate, and the final Hom equation holds for every t.
6. Every derived object has a K-injective representative and every derived map into it
has a homotopy representative. The equalities therefore hold without restrictions on
M, N or t. All comparisons and adjunction Hom bijections are natural. No boundedness,
flatness, torsion, properness or finiteness assumption was used. -/
theorem etaleUnboundedRestrictionAdjunct
    {R B : Type (u + 1)} [CommRing R] [CommRing B] (φ : R →+* B)
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) :
    ∃ v : R((lowerStar (ModuleCat.{u + 1} B) p)) ⋙ (Sheaf.restrictScalars Y.smallEtaleTopology
      φ).mapDerivedCategory ≅ (Sheaf.restrictScalars Z.smallEtaleTopology φ).mapDerivedCategory ⋙
      R((lowerStar (ModuleCat.{u + 1} R) p)),
      v.hom = scalarRestrictionDirectImageMap φ p ∧
      (∀ (I : CochainComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ)
        [I.IsKInjective]
        (J : CochainComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ)
        [J.IsKInjective]
        (j : ((Sheaf.restrictScalars Z.smallEtaleTopology φ).mapHomologicalComplex (.up ℤ)).obj I
          ⟶ J) [QuasiIso j],
        QuasiIso (((lowerStar (ModuleCat.{u + 1} R) p).mapHomologicalComplex (.up ℤ)).map j) ∧
        (Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategory.map
            ((lowerStar (ModuleCat.{u + 1} B) p).rightDerivedFunctorUnit.app
              ((HomotopyCategory.quotient _ _).obj I)) ≫
          v.hom.app (DerivedCategory.Q.obj I) =
        (Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategoryFactorsh.hom.app
            (((lowerStar (ModuleCat.{u + 1} B) p).mapHomotopyCategory (.up ℤ)).obj
              ((HomotopyCategory.quotient _ _).obj I)) ≫
          DerivedCategory.Qh.map (((Functor.mapHomotopyCategoryCompIso
            (lowerStarRestrictScalarsIso φ p) (.up ℤ) ≪≫ (Functor.mapHomotopyCategoryCompIso
            (Iso.refl ((Sheaf.restrictScalars Z.smallEtaleTopology φ) ⋙ (lowerStar (ModuleCat.{u +
            1} R) p))) (.up ℤ)).symm).hom).app ((HomotopyCategory.quotient _ _).obj I)) ≫
          DerivedCategory.Qh.map (((lowerStar (ModuleCat.{u + 1} R) p).mapHomotopyCategory (.up
            ℤ)).map
            ((HomotopyCategory.quotient _ _).map j)) ≫
          (lowerStar (ModuleCat.{u + 1} R) p).rightDerivedFunctorUnit.app
            ((HomotopyCategory.quotient _ _).obj J) ≫
          R((lowerStar (ModuleCat.{u + 1} R) p)).map (inv (DerivedCategory.Q.map j) ≫
            (Sheaf.restrictScalars Z.smallEtaleTopology φ).mapDerivedCategoryFactorsh.inv.app
              ((HomotopyCategory.quotient _ _).obj I))) ∧
      ∀ (M : DerivedCategoryModule B Y) (N : DerivedCategoryModule B Z)
        (t : L(upperStar (ModuleCat.{u + 1} B) p).obj M ⟶ N),
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} R) p).homEquiv _ _
            ((scalarRestrictionPullbackIso φ p).hom.app M ≫ (Sheaf.restrictScalars
              Z.smallEtaleTopology φ).mapDerivedCategory.map t) =
          (Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategory.map
              ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) p).homEquiv M N t) ≫
            v.hom.app N := by
  sorry

end AlgebraicGeometry.Etale
