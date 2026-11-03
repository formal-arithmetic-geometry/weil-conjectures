/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingBundleSectionOrientationData
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackNormalization
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
import WeilConjectures.CategoryTheory.IntTensorFamilyIso
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.Derived.Shift
import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import Mathlib.Logic.Small.Defs
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteConstantUnitSquare
import WeilConjectures.AlgebraicGeometry.EtaleSectionUnitNormalization
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalMaps
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedCartierKummerSupplement
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.AlgebraicGeometry.EtaleDiagonalSectionCoherence
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceCounit
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Data
import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
import WeilConjectures.CategoryTheory.SectionConjugateComparison
import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.SectionProjectionUnitSupplement
import WeilConjectures.AlgebraicGeometry.EtaleTensorTraceBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
import WeilConjectures.AlgebraicGeometry.EtaleCanonicalTensorComparison
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal
import WeilConjectures.CategoryTheory.DerivedSingleUnit
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackComparison
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteConstantPullbackHom
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackHom

/-! # The canonical bundle projection at the coefficient unit

Source: sk-thm-dnc, final comparison with vector-bundle purity;
thm-amb-vector-bundle-purity, opening paragraph.
(blueprint: lem-trf-bundle-section-projection-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Etale

attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence

attribute [local implicit_reducible] Scheme.Modules ordinaryFiniteDegreeZero
  ordinaryFiniteSingleFunctor constantSheaf
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20002] Etale.sheafMonoidalCategory Etale.sheafBraidedCategory
attribute [local implicit_reducible] Etale.sheafMonoidalCategory Etale.sheafBraidedCategory

private theorem iso_hom_eq_id_of_inv_eq_id {C : Type*} [Category C] (X : C) (e : X ≅ X)
    (h : e.inv = 𝟙 _) : e.hom = 𝟙 _ := by
  calc
    e.hom = e.hom ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = e.hom ≫ e.inv := by rw [h]
    _ = 𝟙 _ := e.hom_inv_id

private theorem unit_hom (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) T).hom = 𝟙 _ := by
  exact iso_hom_eq_id_of_inv_eq_id _ _ (singleFunctorObjUnitIso_inv _ _)

private theorem coefficient_first_unit
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D]
    (F : C ⥤ D) (W P : C) (U : D) (a : U ⟶ 𝟙_ D) (e : P ⟶ 𝟙_ C)
    (π : F.obj W ⊗ U ⟶ F.obj (W ⊗ P))
    (hπ : π ≫ F.map (W ◁ e ≫ (ρ_ W).hom) =
      F.obj W ◁ a ≫ (ρ_ (F.obj W)).hom) :
    ((β_ U (F.obj W)).hom ≫ π ≫ F.map (β_ W P).hom) ≫
      F.map (e ▷ W ≫ (λ_ W).hom) = a ▷ F.obj W ≫ (λ_ (F.obj W)).hom := by
  have h : (β_ W P).hom ≫ e ▷ W ≫ (λ_ W).hom =
      W ◁ e ≫ (ρ_ W).hom := by
    rw [← BraidedCategory.braiding_naturality_right_assoc, braiding_leftUnitor]
  simp only [Category.assoc, ← F.map_comp]
  rw [h, hπ, ← BraidedCategory.braiding_naturality_left_assoc, braiding_rightUnitor]

private theorem derived_coefficient_first_unit
    (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (X Y : Scheme.{u})
    (F : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B) ⥤
      _root_.DerivedCategory (Sheaf Y.smallEtaleTopology B))
    (G : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology B) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology B))
    (W : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B))
    (π : (derivedTensor B Y).obj (F.obj W) ⟶ G ⋙ (derivedTensor B X).obj W ⋙ F)
    (e : G.obj (𝟙_ _) ⟶ 𝟙_ _)
    (hπ : π.app (𝟙_ _) ≫ F.map (((derivedTensor B X).obj W).map e ≫
        (derivedTensorRightUnitor B X W).hom) =
      (derivedTensorRightUnitor B Y (F.obj W)).hom)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology B)) (a : K ⟶ 𝟙_ _) :
    (((derivedTensorSymmetry B Y).hom.app K).app (F.obj W) ≫ π.app K ≫
      F.map (((derivedTensorSymmetry B X).hom.app W).app (G.obj K))) ≫
        F.map (((derivedTensor B X).map (G.map a ≫ e)).app W ≫
          (derivedTensorLeftUnitor B X W).hom) =
      ((derivedTensor B Y).map a).app (F.obj W) ≫
        (derivedTensorLeftUnitor B Y (F.obj W)).hom := by
  have hn := π.naturality a
  simp only [Functor.comp_map] at hn
  have hp : π.app K ≫ F.map (((derivedTensor B X).obj W).map (G.map a ≫ e) ≫
      (derivedTensorRightUnitor B X W).hom) =
      ((derivedTensor B Y).obj (F.obj W)).map a ≫
        (derivedTensorRightUnitor B Y (F.obj W)).hom := by
    calc
      _ = (π.app K ≫ F.map (((derivedTensor B X).obj W).map (G.map a))) ≫
          F.map (((derivedTensor B X).obj W).map e ≫
            (derivedTensorRightUnitor B X W).hom) := by
        simp only [Functor.map_comp, Category.assoc]
      _ = (((derivedTensor B Y).obj (F.obj W)).map a ≫ π.app (𝟙_ _)) ≫
          F.map (((derivedTensor B X).obj W).map e ≫
            (derivedTensorRightUnitor B X W).hom) := by rw [← hn]
      _ = _ := by rw [Category.assoc, hπ]
  let := _root_.DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology B)
  let := _root_.DerivedCategory.braidedCategory' (Sheaf Y.smallEtaleTopology B)
  simpa only [derivedTensorLeftUnitor, derivedTensorRightUnitor, derivedTensorSymmetry,
    _root_.DerivedCategory.canonicalTensorSymmetry, BraidedCategory.curriedBraidingNatIso,
    NatIso.ofComponents_hom_app, derivedTensor, curriedTensor_obj_obj,
    curriedTensor_map_app, Functor.flip_obj_obj] using
      coefficient_first_unit F W (G.obj K) K a (G.map a ≫ e) (π.app K) hp

private theorem compact_projection_unit (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (W : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    compactProjectionMapCoeffFirst A f (ordinaryFiniteUnit A Y) W ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
          ((((derivedTensor (ModuleCat.{u + 1} A) X).mapIso
            (ordinaryFiniteUnitPullback A f)).app W ≪≫
              derivedTensorLeftUnitor (ModuleCat.{u + 1} A) X W).hom) =
      (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) Y
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj W)).hom := by
  let F := rightDerivedLowerShriek (ModuleCat.{u + 1} A) f
  let G := ordinaryFinitePullback A f
  let π : (derivedTensor (ModuleCat.{u + 1} A) Y).obj (F.obj W) ⟶
      G ⋙ (derivedTensor (ModuleCat.{u + 1} A) X).obj W ⋙ F :=
    (projectionMap (ModuleCat.{u + 1} A) f).app W
  have h := derived_coefficient_first_unit (ModuleCat.{u + 1} A) X Y F G W π
    (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f).hom
    (projectionMap_rightUnitality (ModuleCat.{u + 1} A) f W)
    (ordinaryFiniteUnit A Y) (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) Y).hom
  have hu := ordinaryFiniteUnitPullback_hom_unit A f
  rw [← hu] at h
  erw [unit_hom A X, unit_hom A Y, Category.comp_id,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at h
  convert h using 1
  · simp only [compactProjectionMapCoeffFirst, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
      Functor.map_comp, Category.assoc, F, G, π, ordinaryFinitePullback]

/-- At the scalar unit, the specified projection followed by the canonical source unit
identification is exactly the compact-support left unitor. This assertion involves no
integration trace, exceptional adjoint, or inverse projection.
Source: sk-thm-dnc, final comparison with vector-bundle purity;
thm-amb-vector-bundle-purity, opening paragraph.
(blueprint: lem-trf-bundle-section-projection-unit).

Proof: Expand the coefficient-first projection as target symmetry, the ordinary
projection, and source symmetry. The canonical pullback of the scalar unit equals the
monoidal unit map of derived inverse image: apply the single-functor unit comparison
and cancel its identity components. Naturality of the source braiding moves this unit
map before the braiding. The source left unitor then becomes the right unitor.
The right-unit equation for the ordinary projection identifies the resulting composite
with the target right unitor. The outer braiding changes this into the target left
unitor. These equations hold for every rank, including zero, and the empty base. -/
theorem bundleSectionProjection_unit (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    vectorBundlePurityProjectionMap A N hA S d M (ordinaryFiniteUnit A S) ≫
        (vectorBundlePurityLower A S d M).map
          (bundleSectionPurityUnitIso N A hA S d M).hom =
      (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) S
        (vectorIntegrationSource A N hA S d M)).hom := by
  exact compact_projection_unit A (VectorBundleZeroSection.π S d M)
    (vectorIntegrationCoefficient A N hA S d M)

end AlgebraicGeometry.Etale
