/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
public import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingData
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothTensorDuality
import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleExceptionalObjectComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
public import WeilConjectures.AlgebraicGeometry.FiniteFieldPrimePowerUnit
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteNormalizedOrientationScalar
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalChart
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalConservativity
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization

/-! # Units, composition and purity under finite coefficient change

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-compatibilities.md and its proof
(blueprint: det-sp-reduction-compatibilities).

The first two identities use the intrinsic constant-ring Dctf adjunctions. The third
uses the equivalent fixed-coefficient presentation of the general-ring purity node,
including its actual diagonal/Rees/integration normalization. No flatness is assumed.

## Main statements

* `reductionCompatibilities_unit`: coefficient change preserves the adjunction unit.
* `reductionCompatibilities_composition`: the exceptional comparisons satisfy the cocycle.
* `reductionCompatibilities_purity`: coefficient change preserves normalized smooth purity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity
open MonoidalCategory

-- The comparison-origin and tensor-naturality arguments are independent of
-- the finite-level purity assembly and its dimension-zero normalization.
private theorem compatibilityIntrinsicOrigin
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) [IsNoetherian T]
    (K : proCategory A T) (hK : IsCtf A T K) :
    ∃ K₀ : DerivedCategoryModule A T,
      DerivedCategory.boundedConstructibleFiniteTor A T K₀ ∧
      Nonempty ((comparison A T).obj K₀ ≅ K) := by
  obtain ⟨a, b, hab, hv⟩ := hK.2.1
  have hbd : _root_.DerivedCategory.TStructure.t.bounded K :=
    ⟨⟨a, (_root_.DerivedCategory.isGE_iff K a).mpr
      (fun i hi ↦ hv i (Or.inl hi))⟩,
     ⟨b, (_root_.DerivedCategory.isLE_iff K b).mpr
      (fun i hi ↦ hv i (Or.inr hi))⟩⟩
  have hc := ProEtale.exceptionalTransport_constructible_comparison A T
  obtain ⟨K₀, hK₀, ⟨e⟩⟩ := (congrFun hc K).mp ⟨hbd, hK.1⟩
  have hbc : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T K₀ := by
    obtain ⟨hc, a, b, _, hv⟩ := hK₀
    exact ⟨⟨⟨a, (_root_.DerivedCategory.isGE_iff K₀ a).mpr
      (fun i hi ↦ hv i (Or.inl hi))⟩,
      ⟨b, (_root_.DerivedCategory.isLE_iff K₀ b).mpr
        (fun i hi ↦ hv i (Or.inr hi))⟩⟩,
      fun i ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hc i)⟩
  refine ⟨K₀, ⟨hbc, ?_⟩, ⟨e⟩⟩
  obtain ⟨c, d, hcd, ht⟩ := hK.2.2
  refine ⟨c, d, ?_⟩
  apply (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff c d K₀).mp
  exact (_root_.DerivedCategory.torAmplitudeIn _ c d).prop_of_iso e.symm ht

private theorem compatibilityIntrinsicOriginCounit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) [IsNoetherian T]
    (K : proCategory A T) (hK : IsCtf A T K) :
    IsIso ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).counit.app K) := by
  obtain ⟨K₀, hK₀, ⟨e⟩⟩ := compatibilityIntrinsicOrigin A T K hK
  let adj := ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) T
  have hp : _root_.DerivedCategory.TStructure.t.plus K₀ := hK₀.1.1.1
  have := ProEtale.isIso_derivedComparisonAdjunction_unit_app (ModuleCat A) T K₀ hp
  have hu : IsIso ((comparison A T).map (adj.unit.app K₀)) := inferInstance
  have hc : IsIso (adj.counit.app ((comparison A T).obj K₀)) :=
    IsIso.of_isIso_fac_left (adj.left_triangle_components K₀)
  exact (NatTrans.isIso_app_iff_of_iso adj.counit e).mp hc

private theorem compatibilityActualOriginCtf
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) [IsNoetherian T]
    (K : proCategory A T) (hK : IsCtf A T K) :
    DerivedCategory.boundedConstructibleFiniteTor A T ((origin A T).obj K) := by
  obtain ⟨K₀, hK₀, ⟨e⟩⟩ := compatibilityIntrinsicOrigin A T K hK
  have := ProEtale.isIso_derivedComparisonAdjunction_unit_app (ModuleCat A) T K₀
    hK₀.1.1.1
  let q : K₀ ≅ (origin A T).obj K :=
    asIso ((ProEtale.derivedComparisonAdjunction (ModuleCat A) T).unit.app K₀) ≪≫
      (origin A T).mapIso e
  exact ⟨(DerivedCategory.boundedConstructible (ModuleCat A) T).prop_of_iso q hK₀.1,
    (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso q hK₀.2⟩

private theorem compatibilityAbstractMateNaturality
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [BraidedCategory C]
    [MonoidalCategory D] [BraidedCategory D]
    (P : D ⥤ C) {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (W : C) (eps : F.obj W ⟶ 𝟙_ D)
    (pi : ∀ K, F.obj (W ⊗ P.obj K) ⟶ F.obj W ⊗ K)
    (hn : ∀ {K L} (a : K ⟶ L),
      F.map (W ◁ P.map a) ≫ pi L = pi K ≫ (F.obj W ◁ a))
    {K L : D} (a : K ⟶ L) :
    (P.map a ▷ W) ≫
      adj.homEquiv _ _ (F.map (β_ (P.obj L) W).hom ≫ pi L ≫
        (β_ (F.obj W) L).hom ≫ (L ◁ eps) ≫ (ρ_ L).hom) =
    adj.homEquiv _ _ (F.map (β_ (P.obj K) W).hom ≫ pi K ≫
        (β_ (F.obj W) K).hom ≫ (K ◁ eps) ≫ (ρ_ K).hom) ≫ G.map a := by
  rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
  apply congrArg (adj.homEquiv _ _)
  rw [← Category.assoc, ← Functor.map_comp,
    BraidedCategory.braiding_naturality_left, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (hn a)]
  rw [BraidedCategory.braiding_naturality_right_assoc,
    ← whisker_exchange_assoc, rightUnitor_naturality]

private theorem compatibilityDirectNaturality
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    [hPF : IsIso (projectionMap (ModuleCat.{u + 1} A) f)]
    {K L : _root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (a : K ⟶ L) :
    ((derivedTensor (ModuleCat.{u + 1} A) X).map
        ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.map a)).app
        (dualizingComplex A f) ≫ smoothTensorDualityMap A f hPF L =
      smoothTensorDualityMap A f hPF K ≫ (rightDerivedUpperShriek A f).map a := by
  let := smoothTensorCanonicalDerivedBraiding (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
  let := smoothTensorCanonicalDerivedBraiding (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))
  apply compatibilityAbstractMateNaturality
  intro K L a
  have h := (asIso ((projectionMap (ModuleCat.{u + 1} A) f).app
    (dualizingComplex A f))).inv.naturality a
  simpa only [asIso, NatIso.isIso_inv_app,
    rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar,
    derivedTensorRightDerivedLowerShriek, Functor.comp_map,
    Functor.postcompose₂, Functor.whiskeringLeft₂, Functor.whiskeringRight,
    Functor.whiskeringLeft, Functor.whiskerLeft, Functor.whiskerRight,
    Functor.comp_obj, Functor.id_obj, Functor.id_map,
    rightDerivedLowerShriek, rightDerivedLowerShriekOfCompactification,
    derivedTensor_obj_map] using h

private theorem compatibilityOrdinaryGammaNaturality
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (L : DerivedCategoryModule A X)
    (alpha : dualizingComplex A f ≅ L)
    {K K' : DerivedCategoryModule A Y} (a : K ⟶ K') :
    (puritySource A f L).map a ≫ gamma A f L alpha K' =
      gamma A f L alpha K ≫ (rightDerivedUpperShriek A f).map a := by
  change ((derivedTensor (ModuleCat A) X).map
      ((ordinaryFinitePullback A f).map a)).app L ≫ _ = _
  unfold gamma
  have ht := ((derivedTensor (ModuleCat A) X).map
    ((ordinaryFinitePullback A f).map a)).naturality alpha.inv
  rw [← Category.assoc, ← ht, Category.assoc]
  have hn := compatibilityDirectNaturality A f a
  change ((derivedTensor (ModuleCat A) X).map
    ((ordinaryFinitePullback A f).map a)).app (dualizingComplex A f) ≫
      smoothTensorDualityMap A f _ K' =
      smoothTensorDualityMap A f _ K ≫
        (rightDerivedUpperShriek A f).map a at hn
  rw [hn, Category.assoc]

private theorem scalarTargetNaturality
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategoryModule A Y) {L M : DerivedCategoryModule A X} (a : L ⟶ M) :
    (ordinaryScalar φ X).map
        (((derivedTensor (ModuleCat A) X).obj ((ordinaryFinitePullback A f).obj K)).map a) ≫
      compactScalarProjectionTarget φ f K M =
    compactScalarProjectionTarget φ f K L ≫
      ((derivedTensor (ModuleCat B) X).obj
        ((ordinaryFinitePullback B f).obj ((ordinaryScalar φ Y).obj K))).map
          ((ordinaryScalar φ X).map a) := by
  have h := (ExceptionalCoefficients.tensorIso φ X).hom.naturality
    (show (((ordinaryFinitePullback A f).obj K, L) ⟶
      ((ordinaryFinitePullback A f).obj K, M)) from (𝟙 _, a))
  have h' := ((derivedTensor (ModuleCat B) X).map
    ((scalarPullbackIso φ f).inv.app K)).naturality ((ordinaryScalar φ X).map a)
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
    Functor.uncurry_obj_map] at h
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at h
  unfold compactScalarProjectionTarget
  erw [← Category.assoc, h, Category.assoc, h']
  exact (Category.assoc _ _ _).symm

private theorem ordinaryGammaCoefficient
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (N M : ℕ) (hA : (N : A) = 0) (hB : (M : B) = 0) (d : ℕ)
    (e : CoefficientLineComparison φ N M hA hB X)
    (a : dualizingComplex A f ≅ line A N hA X d)
    (b : dualizingComplex B f ≅ line B M hB X d)
    (hab : (ordinaryScalar φ X).map a.inv ≫
      ExceptionalCoefficients.dualizingScalarMap φ f = (e.tensorPower d).hom ≫ b.inv)
    (K : DerivedCategoryModule A Y) :
    (ordinaryScalar φ X).map (gamma A f _ a K) ≫ ExceptionalCoefficients.mateMap φ f K =
      (pullbackTwistComparison f d e K).hom ≫
        gamma B f _ b ((ordinaryScalar φ Y).obj K) := by
  have ht := ExceptionalCoefficients.tensorCompatibility φ f K
  unfold ExceptionalCoefficients.TensorCompatibility at ht
  simp only [gamma, Functor.map_comp, Category.assoc]
  erw [ht]
  unfold ExceptionalCoefficients.tensorDomainMap
  simp only [Category.assoc]
  erw [reassoc_of% (scalarTargetNaturality φ f K a.inv)]
  erw [← Functor.map_comp_assoc, hab, Functor.map_comp_assoc]
  change compactScalarProjectionTarget φ f K _ ≫
      ((derivedTensor (ModuleCat B) X).obj _).map (e.tensorPower d).hom ≫ _ = _
  simp only [compactScalarProjectionTarget, pullbackTwistComparison, Iso.trans_hom,
    Iso.app_hom, Iso.app_inv, Functor.prod_obj, Functor.mapIso_hom, Iso.symm_hom,
    Category.assoc]
  rfl

private theorem sourceFromOrigin_gamma
    {A : Type (u + 1)} [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (L : DerivedCategoryModule A X)
    (a : dualizingComplex A f ≅ L) (K : proCategory A Y)
    [hc : IsIso ((ProEtale.derivedComparisonAdjunction (ModuleCat A) Y).counit.app K)] :
    sourceFromOrigin A f L K ≫ proGamma A f L a K =
      (comparison A X).map (gamma A f L a ((origin A Y).obj K)) := by
  unfold proGamma
  have hs : sourceFromOrigin A f L K ≫ sourceToOrigin A f L K = 𝟙 _ := by
    dsimp only [sourceFromOrigin, sourceToOrigin, originInverse]
    rw [dif_pos hc, Category.assoc, ← (proSource A f L).map_comp_assoc,
      IsIso.hom_inv_id]
    erw [(proSource A f L).map_id, Category.id_comp, Iso.hom_inv_id]
  rw [← Category.assoc, hs, Category.id_comp]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem scalarOriginCounit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (Y : Scheme.{u}) [IsNoetherian Y]
    (K : proCategory A Y) (hK : IsCtf A Y K) :
    IsIso ((ProEtale.derivedComparisonAdjunction (ModuleCat B) Y).counit.app
      ((proScalar φ Y).obj K)) := by
  let a := ProEtale.derivedComparisonAdjunction (ModuleCat A) Y
  let b := ProEtale.derivedComparisonAdjunction (ModuleCat B) Y
  have : IsIso (a.counit.app K) := compatibilityIntrinsicOriginCounit A Y K hK
  have hplus := ExceptionalCoefficients.scalar_extension_plus_of_finiteTor φ Y
    ((origin A Y).obj K) (compatibilityActualOriginCtf A Y K hK).2
  have := ProEtale.isIso_derivedComparisonAdjunction_unit_app (ModuleCat B) Y
    ((ordinaryScalar φ Y).obj ((origin A Y).obj K)) hplus
  have : IsIso (b.counit.app ((comparison B Y).obj
      ((ordinaryScalar φ Y).obj ((origin A Y).obj K)))) :=
    IsIso.of_isIso_fac_left (b.left_triangle_components _)
  let e : (comparison B Y).obj ((ordinaryScalar φ Y).obj ((origin A Y).obj K)) ≅
      (proScalar φ Y).obj K :=
    ((ProEtale.pbcComparisonReduction Y φ).app ((origin A Y).obj K)).symm ≪≫
      (proScalar φ Y).mapIso (asIso (a.counit.app K))
  exact (NatTrans.isIso_app_iff_of_iso b.counit e).mp inferInstance

private theorem proGammaCoefficient
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f]
    (N M : ℕ) (hA : (N : A) = 0) (hB : (M : B) = 0) (d : ℕ)
    (e : CoefficientLineComparison φ N M hA hB X)
    (a : dualizingComplex A f ≅ line A N hA X d)
    (b : dualizingComplex B f ≅ line B M hB X d)
    (h : ∀ K : DerivedCategoryModule A Y,
      (ordinaryScalar φ X).map (gamma A f _ a K) ≫
          ExceptionalCoefficients.mateMap φ f K =
        (pullbackTwistComparison f d e K).hom ≫
          gamma B f _ b ((ordinaryScalar φ Y).obj K))
    (K : proCategory A Y) (hK : IsCtf A Y K) :
    (proScalar φ X).map (proGamma A f _ a K) ≫ proCoefficientMap φ f K =
      proLambda f d e K ≫ proGamma B f _ b ((proScalar φ Y).obj K) := by
  have := scalarOriginCounit φ Y K hK
  unfold proLambda
  simp only [Category.assoc, sourceFromOrigin_gamma]
  unfold proGamma proCoefficientMap
  simp only [Functor.map_comp, Category.assoc]
  have hn := (ProEtale.pbcComparisonReduction X φ).hom.naturality
    (gamma A f _ a ((origin A Y).obj K))
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  erw [reassoc_of% hn]
  erw [← (comparison B X).map_comp_assoc, h]
  simp only [Functor.map_comp, Category.assoc]
  have hg := compatibilityOrdinaryGammaNaturality B f _ b (originReductionMap φ Y K)
  have hg' := congrArg (comparison B X).map hg
  simp only [Functor.map_comp] at hg'
  erw [hg']

/-- Scalar extension carries the diagonal/DNC-normalized smooth purity map to the
same map over the new finite ring, under canonical pullback/twist balancing.
`alphaA` and `alphaB` are precisely the orientations of finiteGeneralRingSmoothPurity:
OrientationNormalized retains the actual diagonal mate, the t=1-normalized Rees
comparison and the inverse integration-transposed bundle arrow. `e` retains the
scalar/root-generator normalization; it is not an arbitrary Tate-line isomorphism.
Source: sk-lem-sp-reduction-compatibilities, clause (3)
(blueprint: det-sp-reduction-compatibilities).

Proof (node Steps 1 and 4--8): The scalar monoidal and pullback identifications are
balanced tensor maps on flat K-flat representatives, respecting symmetry and shifts.
For the fixed compactification apply ringedExchangeTensorCoherence to its proper part
and the extension-by-zero tensor comparison to its open part. On the open part both
orders extend sections by zero and multiply the same B-scalars. Pasting gives the
projection/scalar square. FiniteRingCompactSupportProjection makes its projection
maps invertible on the bounded intrinsically constructible inputs omega_A and K.
Transpose the tensor map h using inverse projection followed by the counit at A_Y.
The projection square, naturality and the counit equation defining c identify the
two tensor-map transposes, hence c (h_A)_B = h_B rho. Choose one positive ell-power
annihilating both A and B. finiteGeneralRingSmoothPurity identifies each orientation
with extension of the same prime-power diagonal orientation. Clause (2), already
stated above, gives delta (o_A)_B = o_B; exponent independence permits this common
choice. Finally gamma_R = h_R (1 tensor o_R). Substitute the two equalities to obtain
c (gamma_A)_B = gamma_B lambda. Intrinsic finite-ring comparison identifies the fixed
module presentation used here with the ordinary uncompleted constant-ring category. -/
theorem reductionCompatibilities_purity
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsSeparated f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    [HasCompactification f]
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (n : ℕ) (_hn : 1 ≤ n)
    (hA : ((ℓ ^ n : ℕ) : ULift.{u + 1, u} A) = 0)
    (hB : ((ℓ ^ n : ℕ) : ULift.{u + 1, u} B) = 0)
    (geometry : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst f f) (pullback.diagonal f))
    (alphaA : Etale.dualizingComplex (ULift.{u + 1, u} A) f ≅
      Etale.FiniteSmoothPurity.line (ULift.{u + 1, u} A) (ℓ ^ n) hA X d)
    (alphaB : Etale.dualizingComplex (ULift.{u + 1, u} B) f ≅
      Etale.FiniteSmoothPurity.line (ULift.{u + 1, u} B) (ℓ ^ n) hB X d)
    (_ha : @Etale.FiniteSmoothPurity.OrientationNormalized (ULift.{u + 1, u} A) _ _
      (ℓ ^ n) (pow_pos (Fact.out : ℓ.Prime).pos n) hA X Y
      { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
          (X ↘ Spec (.of D.k))
        toCompactSpace := QuasiCompact.compactSpace_of_compactSpace
          (X ↘ Spec (.of D.k)) } f _
      (@quasiCompact_of_compactSpace X Y f
        (QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k)))
        (quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of D.k)))) _ d geometry
      (finiteFieldPrimePower_isUnit D ℓ hℓ n
        (X ↘ Spec (.of D.k))) alphaA)
    (_hb : @Etale.FiniteSmoothPurity.OrientationNormalized (ULift.{u + 1, u} B) _ _
      (ℓ ^ n) (pow_pos (Fact.out : ℓ.Prime).pos n) hB X Y
      { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
          (X ↘ Spec (.of D.k))
        toCompactSpace := QuasiCompact.compactSpace_of_compactSpace
          (X ↘ Spec (.of D.k)) } f _
      (@quasiCompact_of_compactSpace X Y f
        (QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k)))
        (quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of D.k)))) _ d geometry
      (finiteFieldPrimePower_isUnit D ℓ hℓ n
        (X ↘ Spec (.of D.k))) alphaB)
    (e : Etale.FiniteSmoothPurity.CoefficientLineComparison
      (RingHom.ulift.{u + 1, u + 1, u, u} φ) (ℓ ^ n) (ℓ ^ n) hA hB X)
    (K : Etale.FiniteSmoothPurity.proCategory (ULift.{u + 1, u} A) Y)
    (_hK : Etale.FiniteSmoothPurity.IsCtf (ULift.{u + 1, u} A) Y K) :
    (Etale.FiniteSmoothPurity.proScalar (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).map
        (Etale.FiniteSmoothPurity.proGamma (ULift.{u + 1, u} A) f _ alphaA K) ≫
        Etale.FiniteSmoothPurity.proCoefficientMap
          (RingHom.ulift.{u + 1, u + 1, u, u} φ) f K =
      Etale.FiniteSmoothPurity.proLambda f d e K ≫
        Etale.FiniteSmoothPurity.proGamma (ULift.{u + 1, u} B) f _ alphaB
          ((Etale.FiniteSmoothPurity.proScalar
            (RingHom.ulift.{u + 1, u + 1, u, u} φ) Y).obj K) := by
  let : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
        (X ↘ Spec (.of D.k))
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace
        (X ↘ Spec (.of D.k)) }
  let : IsNoetherian Y :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
        (Y ↘ Spec (.of D.k))
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace
        (Y ↘ Spec (.of D.k)) }
  let : QuasiCompact f :=
    @quasiCompact_of_compactSpace X Y f
      (QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k)))
      (quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of D.k)))
  have : Smooth f := SmoothOfRelativeDimension.smooth d f
  have : LocallyOfFiniteType f := inferInstance
  have ho := Etale.FiniteSmoothPurity.normalizedOrientation_scalar
    (RingHom.ulift.{u + 1, u + 1, u, u} φ) (ℓ ^ n) (ℓ ^ n)
    (pow_pos (Fact.out : ℓ.Prime).pos n) (pow_pos (Fact.out : ℓ.Prime).pos n)
    (dvd_refl _) hA hB
    (finiteFieldPrimePower_isUnit D ℓ hℓ n
      (Y ↘ Spec (.of D.k))) f d geometry
    (finiteFieldPrimePower_isUnit D ℓ hℓ n
      (X ↘ Spec (.of D.k)))
    (finiteFieldPrimePower_isUnit D ℓ hℓ n
      (X ↘ Spec (.of D.k))) alphaA alphaB _ha _hb e
  apply Etale.FiniteSmoothPurity.proGammaCoefficient
    (RingHom.ulift.{u + 1, u + 1, u, u} φ) f (ℓ ^ n) (ℓ ^ n) hA hB d e
      alphaA alphaB _ K _hK
  intro L
  exact Etale.FiniteSmoothPurity.ordinaryGammaCoefficient
    (RingHom.ulift.{u + 1, u + 1, u, u} φ) f (ℓ ^ n) (ℓ ^ n) hA hB d e
      alphaA alphaB ho L

end AlgebraicGeometry.Etale.FiniteSmoothPurity

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale
