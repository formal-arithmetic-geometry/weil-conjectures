/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.VectorTensorSiteEquations

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.VectorBundleZeroSection.VectorBundleZeroSection
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDerivedPullbackFixed
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
public import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import WeilConjectures.CategoryTheory.IntTensorFamilyIso
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierKummerMap
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
public import WeilConjectures.AlgebraicGeometry.Geo.GeoP1Cohomology
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegration
public import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceTopTrace
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorBundlePurity
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
import all WeilConjectures.AlgebraicGeometry.Geo.GeoP1Cohomology
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.VectorLocalTraceExponent
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.SupportedProjectiveChernComparison
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.OrderedIntegrationComparison
import all WeilConjectures.AlgebraicGeometry.Comparison.ComparisonOpenTensorCoherence
public import WeilConjectures.AlgebraicGeometry.Open.OpenProjectionSiteTransport
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedSiteAdjunctionTranspose
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundlePurity
import all WeilConjectures.AlgebraicGeometry.Vector.VectorBundlePurity
import all WeilConjectures.AlgebraicGeometry.Bounded.BoundedSiteAdjunctionTranspose
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.VectorTensorProjectionComparison
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.VectorTensorOrdinaryNormalization
public import WeilConjectures.AlgebraicGeometry.Sp.SpDirectImageEtaleMate

/-! # Site comparison of normalized vector-bundle integration
Source: Stacks 099R, 09AF and 0B65; main-20261015, vector-bundle integration
(blueprint: lem-pur-vector-integration-site-comparison).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite
variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)

/-- The displayed canonical comparison equations, packaged as a proposition.
Source: Stacks 099R, 09AF, 0B65 and the vector-bundle integration formulas
(blueprint: lem-pur-vector-integration-site-comparison). -/
def ProjectiveCompatibility (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (hI : (ProjectiveLine.infinity S).ker.IsInvertible)
    (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) : Prop :=
    ((comparison (Scheme.finiteTateCoefficient l E n) S).map
        (Etale.projectiveLineTraceDatum (l ^ (r + 1))
          (pow_pos (Fact.out : l.Prime).pos _) _ hA S
          (by simpa only [Nat.cast_pow] using hS.pow (r + 1))).decomposition.hom ≫
      (directImage (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S ↘ S)
        (linePlus l E n r hA (ProjectiveLine S))).hom =
      projectiveSum l E n r hA S ≫ projectiveB l E n S hS hI r hA) ∧
    ((directImage (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S ↘ S)
        (linePlus l E n r hA (ProjectiveLine S))).hom ≫
      projectiveTrace l E n S hS hI r hA =
      (comparison (Scheme.finiteTateCoefficient l E n) S).map
        (Etale.ordinaryFiniteProjectiveLineTrace (l ^ (r + 1))
          (pow_pos (Fact.out : l.Prime).pos _) _ hA S
          (by simpa only [Nat.cast_pow] using hS.pow (r + 1)))) ∧
    projectiveH l E n S hS hI r hA ≫ projectiveTrace l E n S hS hI r hA =
      𝟙 (unit (Scheme.finiteTateCoefficient l E n) S)

private theorem mate_adjunct
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (b : L' ⊣ R') {U : C ⥤ C'} {V : D ⥤ D'}
    (e : U ⋙ L' ≅ L ⋙ V) {X : C} {Y : D} (g : L.obj X ⟶ Y) :
    U.map (a.homEquiv X Y g) ≫ (mateEquiv a b e.hom).app Y =
      b.homEquiv _ _ (e.hom.app X ≫ V.map g) := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  have hn := (mateEquiv a b e.hom).naturality g
  change U.map (R.map g) ≫ (mateEquiv a b e.hom).app Y =
    (mateEquiv a b e.hom).app (L.obj X) ≫ R'.map (V.map g) at hn
  rw [hn]
  rw [← Category.assoc, unit_mateEquiv]
  simp only [Functor.id_obj, Category.assoc]

-- Reuse the proved GeoP1Cohomology calculations as local private lemmas.

private theorem vector_mate_app_homEquiv
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ H} {R' : H ⥤ E}
    {G : C ⥤ E} {F : D ⥤ H} (a : L ⊣ R) (b : L' ⊣ R')
    (α : G ⋙ L' ⟶ L ⋙ F) (K : D) :
    (mateEquiv a b α).app K = b.homEquiv _ _
      (α.app (R.obj K) ≫ F.map (a.counit.app K)) := by
  simp [mateEquiv_apply, Adjunction.homEquiv_unit]

private theorem vector_pullComparison_eq (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    geoP1PullComparison A f = BoundaryComparison.pullbackSquare (ModuleCat.{u + 1} A) f := by
  unfold geoP1PullComparison BoundaryComparison.pullbackSquare
    leftDerivedUpperStarIsoMapDerivedCategory Etale.leftDerivedUpperStarIsoMapDerivedCategory
  rfl

private theorem vector_pushComparison_mate (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K : Etale.DerivedCategoryModule A X) :
    geoP1PushComparison A f K =
      (BoundaryComparison.directImageMate (ModuleCat.{u + 1} A) f).app K := by
  unfold geoP1PushComparison BoundaryComparison.directImageMate
  rw [vector_mate_app_homEquiv]
  rw [vector_pullComparison_eq]
  rfl

private theorem vector_sp_included_counit
    (C : Type*) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) C)) :
    (upperStar C f).mapDerivedCategory.map
        ((lowerStar C f).rightDerivedFunctorPlusCompatibility.hom.app J) ≫
      ((upperStarLowerStarAdjunction C f).derivedAdjunction.ofNatIsoLeft
        (upperStar C f).leftDerivedFunctorIsoMapDerivedCategory).counit.app J.obj =
    DerivedCategory.Plus.ι.map
      ((derivedUpperStarLowerStarAdjunctionPlus C f).counit.app J) := by
  simp only [derivedUpperStarLowerStarAdjunctionPlus, Adjunction.derivedAdjunctionPlus,
    Adjunction.map_restrictFullyFaithful_counit_app,
    Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_inv, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp]
  rfl

private theorem vector_sp_included_etale_counit
    (C : Type*) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : DerivedCategory.Plus (Sheaf X.smallEtaleTopology C)) :
    (Etale.upperStar C f).mapDerivedCategory.map
        ((Etale.lowerStar C f).rightDerivedFunctorPlusCompatibility.hom.app J) ≫
      ((Etale.upperStarLowerStarAdjunction C f).derivedAdjunction.ofNatIsoLeft
        (Etale.upperStar C f).leftDerivedFunctorIsoMapDerivedCategory).counit.app J.obj =
    DerivedCategory.Plus.ι.map
      ((Etale.derivedUpperStarLowerStarAdjunctionPlus C f).counit.app J) := by
  simp only [Etale.derivedUpperStarLowerStarAdjunctionPlus, Adjunction.derivedAdjunctionPlus,
    Adjunction.map_restrictFullyFaithful_counit_app,
    Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_inv, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp]
  rfl

private theorem vector_geoP1_sp_comparison_hom
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hK : ∃ n : ℤ, K.IsGE n) :
    (spDirectImageComparisonIso A f K hK).hom =
      (BoundaryComparison.directImageMate (ModuleCat.{u + 1} A) f).app K := by
  let J : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨K, hK⟩
  let C := ModuleCat.{u + 1} A
  let E := Etale.upperStar C f
  let P := upperStar C f
  let DX := (comparisonUpperStar C X).mapDerivedCategory
  let DY := (comparisonUpperStar C Y).mapDerivedCategory
  let eps := ((upperStarLowerStarAdjunction C f).derivedAdjunction.ofNatIsoLeft
    P.leftDerivedFunctorIsoMapDerivedCategory).counit
  let epse := ((Etale.upperStarLowerStarAdjunction C f).derivedAdjunction.ofNatIsoLeft
    E.leftDerivedFunctorIsoMapDerivedCategory).counit
  have hn := congrArg DerivedCategory.Plus.ι.map
    (fixedComparisonDirectImageMatePlus_counit A f J)
  have hpull : DerivedCategory.Plus.ι.map
      ((fixedComparisonPullbackPlus A f).hom.app
        ((Etale.rightDerivedLowerStarPlus C f).obj J)) =
      ((Functor.mapDerivedCategoryCompIso E (comparisonUpperStar C X)).inv ≫
        (Functor.mapDerivedCategoryNatIso
          (comparisonUpperStarCompUpperStarIso C f).symm).hom ≫
        (Functor.mapDerivedCategoryCompIso (comparisonUpperStar C Y) P).hom).app
          (((Etale.lowerStar C f).rightDerivedFunctorPlus.obj J).obj) := by
    simp only [fixedComparisonPullbackPlus, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.map_comp]
    have he : DerivedCategory.Plus.ι.mapIso
        ((Functor.mapDerivedCategoryPlusCompIso E (comparisonUpperStar C X)).app
          ((Etale.rightDerivedLowerStarPlus C f).obj J)) =
        (Functor.mapDerivedCategoryCompIso E (comparisonUpperStar C X)).app
          (((Etale.rightDerivedLowerStarPlus C f).obj J).obj) :=
      Iso.ext (Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app _ _ _)
    have hi := congrArg Iso.inv he
    change DerivedCategory.Plus.ι.map
      ((Functor.mapDerivedCategoryPlusCompIso E (comparisonUpperStar C X)).inv.app
        ((Etale.rightDerivedLowerStarPlus C f).obj J)) = _ at hi
    erw [hi, Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
      Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app]
    rfl
  simp only [Functor.map_comp] at hn
  rw [hpull, ← vector_sp_included_counit C f] at hn
  change _ = DX.map (DerivedCategory.Plus.ι.map
    ((Etale.derivedUpperStarLowerStarAdjunctionPlus C f).counit.app J)) at hn
  rw [← vector_sp_included_etale_counit C f] at hn
  change _ = DX.map (E.mapDerivedCategory.map
    ((Etale.lowerStar C f).rightDerivedFunctorPlusCompatibility.hom.app J) ≫ epse.app K) at hn
  apply ((derivedUpperStarLowerStarAdjunction C f).ofNatIsoLeft
    P.leftDerivedFunctorIsoMapDerivedCategory).homEquiv _ _ |>.symm.injective
  rw [Adjunction.homEquiv_counit]
  rw [Adjunction.homEquiv_ofNatIsoLeft_symm_apply,
    BoundaryComparison.directImageMate, Adjunction.homEquiv_counit, mateEquiv_counit]
  dsimp only [spDirectImageComparisonIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv, asIso_hom,
    Functor.mapDerivedCategoryPlusCompatibility, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app]
  let q := (Functor.mapDerivedCategoryCompIso E (comparisonUpperStar C X)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (comparisonUpperStarCompUpperStarIso C f).symm ≪≫
    Functor.mapDerivedCategoryCompIso (comparisonUpperStar C Y) P
  let r := (Etale.lowerStar C f).rightDerivedFunctorPlusCompatibility.app J
  let b := DerivedCategory.Plus.ι.map ((fixedComparisonDirectImageMatePlus A f).app J)
  let c := (lowerStar C f).rightDerivedFunctorPlusCompatibility.hom.app
    ((comparisonUpperStar C X).mapDerivedCategoryPlus.obj J)
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  change P.mapDerivedCategory.map (DY.map r.inv ≫ b ≫ c) ≫ eps.app (DX.obj K) = _
  have hnorm : P.mapDerivedCategory.map b ≫ P.mapDerivedCategory.map c ≫
      eps.app (DX.obj K) = q.inv.app ((Etale.rightDerivedLowerStarPlus C f).obj J).obj ≫
        DX.map (E.mapDerivedCategory.map r.hom ≫ epse.app K) := by
    change q.hom.app _ ≫ P.mapDerivedCategory.map b ≫ P.mapDerivedCategory.map c ≫
      eps.app (DX.obj K) = _ at hn
    apply (cancel_epi (q.hom.app _)).1
    erw [Iso.hom_inv_id_app_assoc]
    exact hn
  simp only [Functor.map_comp, Category.assoc]
  rw [hnorm]
  erw [q.inv.naturality_assoc]
  simp only [Functor.comp_map, Functor.map_comp]
  change q.inv.app _ ≫ DX.map (E.mapDerivedCategory.map r.inv) ≫
    DX.map (E.mapDerivedCategory.map r.hom) ≫ DX.map (epse.app K) = _
  rw [← DX.map_comp_assoc, ← E.mapDerivedCategory.map_comp, r.inv_hom_id,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [q, epse, BoundaryComparison.pullbackSquare, Adjunction.ofNatIsoLeft_counit,
    Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp, Category.assoc,
    ]
  erw [Iso.inv_hom_id_app_assoc]
  rfl

private theorem vector_geoP1_pushComparison_eq (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (K : Etale.DerivedCategoryModule A X) (hK : ∃ n : ℤ, K.IsGE n) :
    geoP1PushComparison A f K = (spDirectImageComparisonIso A f K hK).hom := by
  rw [vector_pushComparison_mate]
  exact (vector_geoP1_sp_comparison_hom A f K hK).symm

private theorem vector_pushComparison_plus (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (geoP1Comparison A Y).map
        ((Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlusCompatibility.hom.app K) ≫
      geoP1PushComparison A f K.obj =
    (rightDerivedLowerStarComparisonIso' f (ModuleCat.{u + 1} A)).hom.app K := by
  rw [vector_geoP1_pushComparison_eq A f K.obj K.property]
  simp only [spDirectImageComparisonIso, rightDerivedLowerStarComparisonIso',
    rightDerivedLowerStarComparisonPlusIso, Functor.mapDerivedCategoryPlusCompatibility,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, asIso_hom,
    fixedComparisonDirectImageMatePlus]
  erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id]
  erw [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

private theorem directImage_eq_push (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (J : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (directImage A f J).hom = geoP1PushComparison A f J.obj := by
  unfold directImage
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom]
  rw [← vector_pushComparison_plus A f J]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  change (comparison A Y).map (𝟙 ((Etale.ordinaryFinitePushforward A f).obj J.obj)) ≫
    geoP1PushComparison A f J.obj = _
  exact (congrArg (fun v ↦ v ≫ geoP1PushComparison A f J.obj)
    ((comparison A Y).map_id _)).trans (Category.id_comp _)

private theorem directImage_adjunct (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (K : Etale.DerivedCategoryModule A Y)
    (J : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (g : (Etale.ordinaryFinitePullback A f).obj K ⟶ J.obj) :
    (comparison A Y).map
        ((Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _ g) ≫
      (directImage A f J).hom =
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _
      ((pullback A f).inv.app K ≫ (comparison A X).map g) := by
  have h := mate_adjunct
    (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (geoP1PullComparison A f) g
  rw [vector_mate_app_homEquiv] at h
  rw [directImage_eq_push A f J]
  unfold pullback
  exact h

/-- Comparison carries the ordinary decomposition to the two actual supported-Kummer
components. Source: projective-line trace and Stacks 099R, 0B65
(blueprint: lem-pur-vector-integration-site-comparison).
Proof: the mate's counit equation carries the adjunct of the ordinary Kummer class
to the supported pro-etale class. At the identity it carries the shifted twisted
unit. The two biproduct injections detect equality. Invert the decomposition and
compose with the second projection for the trace equation and its +1 normalization.
-/
theorem projectiveComparison (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (hI : (ProjectiveLine.infinity S).ker.IsInvertible)
    (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
    ProjectiveCompatibility l E n S hS hI r hA := by
  let A := Scheme.finiteTateCoefficient l E n
  let N := l ^ (r + 1)
  let D := Etale.projectiveLineTraceDatum N (pow_pos (Fact.out : l.Prime).pos _) A hA S
    (by simpa only [N, Nat.cast_pow] using hS.pow (r + 1))
  have hu : (comparison A S).map
      (Etale.ordinaryFiniteP1Unit A N hA
        (Etale.projectiveLineTraceTransport N (pow_pos (Fact.out : l.Prime).pos _) A hA)
        S (by simpa only [N, Nat.cast_pow] using hS.pow (r + 1))) ≫
        (directImage A (ProjectiveLine S ↘ S) (linePlus l E n r hA (ProjectiveLine S))).hom =
      projectiveU l E n S hS r hA := by
    unfold Etale.ordinaryFiniteP1Unit projectiveU
    with_unfolding_all
      simpa only [Adjunction.homEquiv_unit, Etale.ordinaryFinitePushforward] using
      directImage_adjunct A (ProjectiveLine S ↘ S) _
        (linePlus l E n r hA (ProjectiveLine S))
        (Etale.ordinaryFiniteShiftedLinePullback A N hA
          (Etale.projectiveLineTraceTransport N (pow_pos (Fact.out : l.Prime).pos _) A hA)
          (ProjectiveLine S ↘ S)
          (by simpa only [N, Nat.cast_pow] using hS.pow (r + 1))).hom
  have hh : (comparison A S).map
      (Etale.ordinaryFiniteP1ChernPushforward A N hA S D.chern) ≫
        (directImage A (ProjectiveLine S ↘ S) (linePlus l E n r hA (ProjectiveLine S))).hom =
      projectiveH l E n S hS hI r hA := by
    have h := directImage_adjunct A (ProjectiveLine S ↘ S)
      (Etale.ordinaryFiniteUnit A S) (linePlus l E n r hA (ProjectiveLine S))
      ((Etale.ordinaryFiniteUnitPullback A (ProjectiveLine S ↘ S)).hom ≫ D.chern)
    rw [Etale.ordinaryFiniteP1ChernPushforward, h]
    unfold projectiveH
    congr 1
    rw [supportedProjectiveChern_comparison l E n S hS hI r hA]
    unfold pullbackUnit geoP1UnitPullback pullback
    simp only [Iso.trans_hom, Iso.symm_inv, Functor.mapIso_hom, Category.assoc]
    rw [← Functor.map_comp]
    with_unfolding_all rfl
  have hb : (comparison A S).map D.decomposition.hom ≫
      (directImage A (ProjectiveLine S ↘ S) (linePlus l E n r hA (ProjectiveLine S))).hom =
      projectiveSum l E n r hA S ≫ projectiveB l E n S hS hI r hA := by
    rw [D.decomposition_hom]
    let := preservesBinaryBiproducts_of_preservesBinaryCoproducts (comparison A S)
    unfold projectiveSum projectiveB
    change _ = ((comparison A S).mapBiprod
      ((Etale.ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)
      (Etale.ordinaryFiniteUnit A S)).hom ≫ _
    apply (cancel_epi ((comparison A S).mapBiprod
      ((Etale.ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)
      (Etale.ordinaryFiniteUnit A S)).inv).mp
    rw [← Category.assoc, biprod.mapBiprod_inv_map_desc, Iso.inv_hom_id_assoc]
    with_unfolding_all
      ext <;> simp only [biprod.inl_desc_assoc, biprod.inr_desc_assoc,
        biprod.inl_desc, biprod.inr_desc, hu, hh]
  refine ⟨hb, ?_, ?_⟩
  · unfold projectiveTrace geoP1Trace Etale.ordinaryFiniteProjectiveLineTrace
    let := projectiveB_isIso l E n S hS hI r hA
    apply (cancel_epi ((comparison A S).map D.decomposition.hom)).mp
    rw [reassoc_of% hb]
    simp only [asIso_inv, IsIso.hom_inv_id_assoc, projectiveSum]
    change _ = (comparison A S).map D.decomposition.hom ≫
      (comparison A S).map (D.decomposition.inv ≫ biprod.snd)
    rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_assoc]
    with_unfolding_all exact biprod.lift_snd _ _
  · unfold projectiveTrace geoP1Trace
    let := projectiveB_isIso l E n S hS hI r hA
    have hi : projectiveH l E n S hS hI r hA =
        biprod.inr ≫ projectiveB l E n S hS hI r hA := by
      simp only [projectiveB, biprod.inr_desc]
    rw [hi]
    simp only [Category.assoc, asIso_inv, IsIso.hom_inv_id_assoc]
    with_unfolding_all exact biprod.inr_snd

private theorem counit_square_of_unit
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (b : L' ⊣ R') {U : C ⥤ C'} {V : D ⥤ D'}
    (e : U ⋙ L' ≅ L ⋙ V) (t : R ⋙ U ≅ V ⋙ R')
    (h : ∀ K, b.unit.app (U.obj K) ≫ R'.map (e.hom.app K) =
      U.map (a.unit.app K) ≫ t.hom.app (L.obj K)) (K : D) :
    V.map (a.counit.app K) = e.inv.app (R.obj K) ≫
      L'.map (t.hom.app K) ≫ b.counit.app (V.obj K) := by
  have hh : e.hom.app (R.obj K) ≫ V.map (a.counit.app K) =
      L'.map (t.hom.app K) ≫ b.counit.app (V.obj K) := by
    apply (b.homEquiv _ _).injective
    simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
    rw [h]
    simp only [Category.assoc]
    have hn := t.hom.naturality (a.counit.app K)
    change U.map (R.map (a.counit.app K)) ≫ t.hom.app K =
      t.hom.app (L.obj (R.obj K)) ≫ R'.map (V.map (a.counit.app K)) at hn
    rw [← hn]
    simp only [← Category.assoc, ← U.map_comp, a.right_triangle_components]
    simp only [Category.assoc]
    rw [b.unit_naturality_assoc]
    simp only [Functor.comp_obj, b.right_triangle_components, Category.comp_id]
    exact (congrArg (fun f ↦ f ≫ t.hom.app K) (U.map_id (R.obj K))).trans
      (Category.id_comp _)
  rw [← cancel_epi (e.hom.app (R.obj K))]
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  rw [hh]

/-- Exact extension comparison preserves the actual open counit.
Source: Stacks 09AF (blueprint: lem-pur-vector-integration-site-comparison).
Proof: both routes restrict to the identity. Transpose using the open adjunction;
its Hom bijection gives equality. Apply termwise to complexes and localize.
-/
theorem openCounitComparison {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (G : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparison A X).map
        (((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) j).ofNatIsoRight
            (Etale.leftDerivedUpperStarIsoMapDerivedCategory
              (ModuleCat.{u + 1} A) j).symm).counit.app G) =
      (openProjectionExtensionComparison A j).hom.app
        ((Etale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor.obj G) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.map
        ((openProjectionRestrictionComparison A j).hom.app G) ≫
      (openAdjunction A j).counit.app ((comparison A X).obj G) := by
  let B := ModuleCat.{u + 1} A
  let a := Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction B j
  let b := derivedOpenImmersionLowerShriekUpperStarAdjunction B j
  let e := (openProjectionExtensionComparison A j).symm
  let t := Functor.mapDerivedCategorySquareIso
    (F₁ := Etale.upperStar B j) (F₂ := comparisonUpperStar B U)
    (G₁ := comparisonUpperStar B X) (G₂ := upperStar B j)
    (supportSiteComparisonCoefficientPullbackIso B j)
  have h := counit_square_of_unit a b e t
    (comparison_derived_extension_mate A j) G
  dsimp only [a, b, e, t] at h
  rw [supportComparison_eq A j] at h
  simp only [openAdjunction, Adjunction.ofNatIsoRight_counit,
    openProjectionRestrictionComparison, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp,
    Iso.symm_hom, Iso.symm_inv, Category.assoc]
  rw [h]
  have hn := (openProjectionExtensionComparison A j).hom.naturality
    ((Etale.leftDerivedUpperStarIsoMapDerivedCategory B j).hom.app G)
  change (comparison A X).map
      ((Etale.openImmersionLowerShriek B j).mapDerivedCategory.map
        ((Etale.leftDerivedUpperStarIsoMapDerivedCategory B j).hom.app G)) ≫
      (openProjectionExtensionComparison A j).hom.app
        ((Etale.upperStar B j).mapDerivedCategory.obj G) =
    (openProjectionExtensionComparison A j).hom.app
        ((Etale.upperStar B j).leftDerivedFunctor.obj G) ≫
      (openImmersionLowerShriek B j).mapDerivedCategory.map
        ((comparison A U).map
          ((Etale.leftDerivedUpperStarIsoMapDerivedCategory B j).hom.app G)) at hn
  simp only [Iso.symm_inv]
  rw [reassoc_of% hn]
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Functor.mapDerivedCategoryNatIso_symm, Functor.map_comp, Category.assoc]
  have hp := (openImmersionLowerShriek B j).mapDerivedCategory.map_comp
    ((leftDerivedUpperStarIsoMapDerivedCategory B j).inv.app ((comparison A X).obj G))
    ((leftDerivedUpperStarIsoMapDerivedCategory B j).hom.app ((comparison A X).obj G))
  rw [Iso.inv_hom_id_app, CategoryTheory.Functor.map_id] at hp
  rw [← reassoc_of% hp]

/-- The displayed canonical comparison equations, packaged as a proposition.
Source: Stacks 099R, 09AF, 0B65 and the vector-bundle integration formulas
(blueprint: lem-pur-vector-integration-site-comparison). -/
def IntegrationCompatibility (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] : Prop :=
    VectorNormalization l E n S r hA d F hS
      (vectorIntegration l E n S r hA d F hS) ∧
    (vectorSite l E n S r hA d F hS).inv ≫
        vectorIntegration l E n S r hA d F hS =
      (comparison (Scheme.finiteTateCoefficient l E n) S).map
        (Etale.vectorBundleIntegration (l ^ (r + 1))
          (pow_pos (Fact.out : l.Prime).pos _) (Scheme.finiteTateCoefficient l E n) hA S
          (by simpa only [Nat.cast_pow] using hS.pow (r + 1)) d F)

private theorem compared_pullback_unit (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K : Etale.DerivedCategoryModule A Y} (g : K ⟶ Etale.ordinaryFiniteUnit A Y) :
    (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.map
        ((comparison A Y).map g) ≫ (pullbackUnit A f).hom =
      (pullback A f).inv.app K ≫ (comparison A X).map
        ((Etale.ordinaryFinitePullback A f).map g ≫
          (Etale.ordinaryFiniteUnitPullback A f).hom) := by
  have hn := (pullback A f).inv.naturality g
  dsimp only [Functor.comp_map] at hn
  unfold pullbackUnit geoP1UnitPullback
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  unfold pullback at hn ⊢
  with_unfolding_all
    erw [← Category.assoc, hn, Category.assoc, ← CategoryTheory.Functor.map_comp]

section TensorComparisonProof
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence
  Functor.mapDerivedCategory Etale.derivedTensor derivedTensor
  derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso compactSupportSiteComparison
attribute [local implicit_reducible] Etale.vectorBundlePurityLower
  Etale.vectorBundlePurityCompactification Etale.vectorIntegrationSource

-- Share elaborated instance proofs using Lean's ordinary proof abstraction cache.
-- This changes only the proof term; the kernel checks the result as usual.
open Lean Meta in
open Lean Meta Elab Tactic
set_option linter.style.multiGoal false in
set_option linter.unusedVariables false in
end TensorComparisonProof

/-- Root-normalized twist comparison, arbitrary scheme pullback, and exponent transitions.
Source: Stacks 03PK and 099R (blueprint: lem-pur-vector-integration-site-comparison).
Proof: finite reduction is induced by root projection after tensoring with A.
Generators determine the comparison, every pullback square, and every exponent
transition. Repeated tensor gives all powers, including the constant zero power.
A common larger exponent compares any two annihilators. No flatness of A is used.
-/
theorem twistCompatibility :
    (∀ (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤))) (r : ℕ)
      (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (k : ℕ),
      Scheme.IsFiniteTateSiteComparison l E n T r hA k (twistComparison l E n T hT r hA k)) ∧
    (∀ (T T' : Scheme.{u}) (v : T' ⟶ T)
      (hT : IsUnit (l : Γ(T, ⊤))) (hT' : IsUnit (l : Γ(T', ⊤)))
      (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (k : ℕ),
      ∃ (c : (Etale.upperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) v).obj
          (Scheme.finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k) ≅
            Scheme.finiteEtaleTateTwist T' (l ^ (r + 1)) _ hA k)
        (d : (ProEtale.upperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) v).obj
          (Scheme.finiteTateProSheaf l E n T k) ≅ Scheme.finiteTateProSheaf l E n T' k),
      Scheme.IsFiniteTateEtalePullback l E n T v r hA k c ∧
      Scheme.IsFiniteTateProPullback l E n T v k d ∧
      (ProEtale.upperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) v).mapIso
          (twistComparison l E n T hT r hA k) ≪≫ d =
        (ProEtale.comparisonUpperStarCompUpperStarIso
          (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) v).app
            (Scheme.finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k) ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) T').mapIso c ≪≫
          twistComparison l E n T' hT' r hA k) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤))) (r r' : ℕ) (_h : r ≤ r')
      (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
      (hA' : ((l ^ (r' + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (k : ℕ),
      ∃! t : Scheme.finiteEtaleTateTwist T (l ^ (r' + 1)) _ hA' k ≅
          Scheme.finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k,
        Scheme.IsFiniteTateEtaleTransition l E n T r r' hA hA' k t ∧
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) T).mapIso t ≪≫
            twistComparison l E n T hT r hA k =
            twistComparison l E n T hT r' hA' k) := by
  unfold twistComparison
  exact ⟨(Scheme.finite_tate_site_descent l E n).choose_spec.1,
    (Scheme.finite_tate_site_descent l E n).choose_spec.2.1,
    (Scheme.finite_tate_site_descent l E n).choose_spec.2.2.1⟩

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
