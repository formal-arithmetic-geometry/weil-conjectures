/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingBundleSectionOrientationData
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackComp
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
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
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
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackHom
import WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarSingle
import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement

/-! # Pasting a section comparison with an isomorphism of its ambient scheme -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local instance] unbounded_has_base_change unbounded_has_proper_exchange

-- The public normalization theorem has extra geometric hypotheses; its formal proof does not.
private theorem exchange_normalization_general
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {v : Y' ⟶ Y} {v' : X' ⟶ X}
    (sq : IsPullback v' f' f v) (c : Compactification f) :
    unboundedEtaleCompactSupportExchange A sq c =
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
        (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
          (IsPullback.of_hasPullback c.g v).toCommSq) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} A)
          (c.isPullback_i_ofIsPullback sq)).inv
        (rightDerivedLowerStar (ModuleCat.{u + 1} A) (c.ofIsPullback sq).g) ≫
      (Functor.associator _ _ _).hom := by
  ext K
  have h := congrArg (fun η ↦ η.app
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj K))
    (exact_exchange_transport A (IsPullback.of_hasPullback c.g v).toCommSq)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h
  simp only [unboundedEtaleCompactSupportExchange,
    rightDerivedLowerShriekOfCompactificationBaseChangeMap,
    derivedOpenImmersionLowerShriekBaseChangeIso, Iso.trans_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.map_comp,
    Category.id_comp, Category.comp_id, Category.assoc]
  dsimp only [rightDerivedLowerShriekOfCompactification, rightDerivedLowerStar,
    Functor.comp_obj, Functor.comp_map] at h ⊢
  simp only [← Functor.map_comp, Iso.inv_hom_id_app]
  simp only [Functor.map_comp]
  rw [← h]
  simp only [Category.assoc]
  rw [((openImmersionLowerShriek (ModuleCat.{u + 1} A)
    (c.ofIsPullback sq).i).mapDerivedCategory).map_id]
  erw [CategoryTheory.Functor.map_id]
  rw [Category.comp_id]
  rfl

private lemma shriek_base_change_general
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {v : Y' ⟶ Y} {v' : X' ⟶ X}
    (sq : IsPullback v' f' f v)
    (c : Compactification f) :
    ((unboundedFormalism A).shriekBaseChangeOfIsPullback sq c).natTrans =
      unboundedEtaleCompactSupportExchange A sq c := by
  let := CompactSupportFormalism.HasBaseChange.isIso_baseChange
    (F := unboundedFormalism A) (c.isPullback_i_ofIsPullback sq)
  have hh : inv ((unboundedFormalism A).baseChange v' (c.ofIsPullback sq).i c.i
      (pullback.fst c.g v) (c.isPullback_i_ofIsPullback sq).w).natTrans =
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} A) (c.isPullback_i_ofIsPullback sq)).inv := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [unbounded_open_base_change]
    exact Iso.hom_inv_id _
  rw [exchange_normalization_general]
  dsimp only [CompactSupportFormalism.shriekBaseChangeOfIsPullback,
    CompactSupportFormalism.shriekBaseChange, ExchangeFormalism.shriekBaseChange,
    TwoSquare.hComp, TwoSquare.natTrans, TwoSquare.mk]
  rw [unbounded_pf_base_change, hh]
  rfl

private lemma chosen_base_change_general
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {v : Y' ⟶ Y} {v' : X' ⟶ X}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f] [QuasiCompact f']
    (sq : IsPullback v' f' f v) :
    ((unboundedFormalism A).lowerShriekBaseChange sq).natTrans =
      unboundedEtaleCompactSupportBaseChange A sq := by
  let B := ModuleCat.{u + 1} A
  let c := HasCompactification.compactification f
  dsimp only [CompactSupportFormalism.lowerShriekBaseChange, TwoSquare.whiskerBottom]
  rw [shriek_base_change_general, unbounded_shriek_iso]
  rw [unboundedEtaleCompactSupportExchange, unboundedEtaleCompactSupportBaseChange,
    rightDerivedLowerShriekBaseChangeMap]
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc]
  apply congrArg (fun t ↦ _ ≫ _ ≫ t)
  exact (rightDerivedLowerShriekIso A (c.ofIsPullback sq)).hom.naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory B v').hom.app K)

private theorem exchange_comp_general
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v' : X' ⟶ X} {w' : X'' ⟶ X'}
    [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f'] [QuasiCompact f'']
    (sq₁ : IsPullback v' f' f v) (sq₂ : IsPullback w' f'' f' w)
    (sq₃ : IsPullback (w' ≫ v') f'' f (w ≫ v)) :
    unboundedEtaleCompactSupportBaseChange A sq₃ =
      Functor.whiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
        (unboundedEtaleUpperStarCompIso A w v).hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (unboundedEtaleCompactSupportBaseChange A sq₁)
        (upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) v').mapDerivedCategory
        (unboundedEtaleCompactSupportBaseChange A sq₂) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (unboundedEtaleUpperStarCompIso A w' v').inv
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f'') := by
  have h := congrArg TwoSquare.natTrans
    (chosenBaseChange_paste_horiz (unboundedFormalism A) sq₁ sq₂ sq₃)
  have hc {S T U : Scheme.{u}} (a : S ⟶ T) (b : T ⟶ U) :
      (unboundedFormalism A).pbComp a b = unboundedEtaleUpperStarCompIso A a b := rfl
  rw [hc, hc] at h
  simp only [chosen_base_change_general, TwoSquare.whiskerLeft,
    TwoSquare.whiskerRight, TwoSquare.vComp, TwoSquare.mk, TwoSquare.natTrans] at h
  change (_ : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
      (upperStar (ModuleCat.{u + 1} A) (w ≫ v)).mapDerivedCategory ⟶
      (upperStar (ModuleCat.{u + 1} A) (w' ≫ v')).mapDerivedCategory ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) f'')) = _ at h
  simp only [Category.assoc] at h
  exact h

attribute [local irreducible] unboundedEtaleCompactSupportBaseChange

set_option backward.isDefEq.respectTransparency true in

private theorem exchange_paste (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v' : X' ⟶ X} {w' : X'' ⟶ X'}
    [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f'] [QuasiCompact f'']
    (sq₁ : IsPullback v' f' f v) (sq₂ : IsPullback w' f'' f' w)
    (K : DerivedCategoryModule A X) :
    (ordinaryFinitePullback A w).map ((rightDerivedLowerShriekBaseChangeMap A sq₁).app K) ≫
        (rightDerivedLowerShriekBaseChangeMap A sq₂).app
          ((ordinaryFinitePullback A v').obj K) =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w v).inv.app _ ≫
        (rightDerivedLowerShriekBaseChangeMap A (sq₂.paste_horiz sq₁)).app K ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f'').map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v').hom.app K) := by
  have h := congr_app (exchange_comp_general A sq₁ sq₂
    (sq₂.paste_horiz sq₁)) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    unboundedEtaleCompactSupportBaseChange,
    unboundedEtaleUpperStarCompIso, Iso.trans_hom, Iso.trans_inv, Functor.map_comp,
    Category.assoc] at h
  apply (cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w v).hom.app _)).mp
  apply (cancel_mono ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f'').map
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v').inv.app K))).mp
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app]
  apply (cancel_epi ((leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} A) (w ≫ v)).inv.app _)).mp
  apply (cancel_mono ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f'').map
    ((leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} A) (w' ≫ v')).hom.app K))).mp
  simp only [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Category.assoc, Iso.inv_hom_id_app_assoc,
    Functor.map_comp]
  simp only [leftDerivedUpperStarIsoMapDerivedCategory, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app, Category.comp_id] at h ⊢
  simp only [Category.id_comp]
  rw [h]
  simp only [Functor.map_comp, ordinaryFinitePullback]
  have hn :=
    (upperStar (ModuleCat.{u + 1} A) w).leftDerivedFunctorIsoMapDerivedCategory.inv.naturality
    ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f').map
      ((upperStar (ModuleCat.{u + 1} A) v').leftDerivedFunctorIsoMapDerivedCategory.hom.app K))
  rw [reassoc_of% hn]
  have he := (rightDerivedLowerShriekBaseChangeMap A sq₂).naturality
    ((upperStar (ModuleCat.{u + 1} A) v').leftDerivedFunctorIsoMapDerivedCategory.hom.app K)
  simp only [Functor.comp_map] at he
  rw [reassoc_of% he]
  rw [← Functor.map_comp_assoc]
  rw [← (upperStar (ModuleCat.{u + 1} A) w').leftDerivedFunctorIsoMapDerivedCategory.hom.naturality]
  simp only [Functor.map_comp, Category.assoc]
  have hlast :=
    (upperStar (ModuleCat.{u + 1} A) w).leftDerivedFunctorIsoMapDerivedCategory.inv.naturality
      ((rightDerivedLowerShriekBaseChangeMap A sq₁).app K)
  simp only [Functor.comp_obj] at hlast
  rw [← reassoc_of% hlast]

-- Pasting the inverse exchanges and taking their exceptional mates.
private theorem exceptional_base_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v' : X' ⟶ X} {w' : X'' ⟶ X'}
    [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f'] [QuasiCompact f'']
    (sq₁ : IsPullback v' f' f v) (sq₂ : IsPullback w' f'' f' w)
    (K : DerivedCategoryModule A Y) :
    (rightDerivedUpperShriekBaseChangeMap A (sq₂.paste_horiz sq₁)).app K =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v').hom.app
        ((rightDerivedUpperShriek A f).obj K) ≫
      (upperStar (ModuleCat.{u + 1} A) w').leftDerivedFunctor.map
        ((rightDerivedUpperShriekBaseChangeMap A sq₁).app K) ≫
      (rightDerivedUpperShriekBaseChangeMap A sq₂).app
        ((upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.obj K) ≫
      (rightDerivedUpperShriek A f'').map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w v).inv.app K) := by
  have := isIso_rightDerivedLowerShriekBaseChangeMap A sq₁
  have := isIso_rightDerivedLowerShriekBaseChangeMap A sq₂
  have := isIso_rightDerivedLowerShriekBaseChangeMap A (sq₂.paste_horiz sq₁)
  let E₁ := rightDerivedLowerShriekBaseChangeMap A sq₁
  let E₂ := rightDerivedLowerShriekBaseChangeMap A sq₂
  let E₃ := rightDerivedLowerShriekBaseChangeMap A (sq₂.paste_horiz sq₁)
  let c := leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w v
  let c' := leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v'
  let δ₁ := TwoSquare.mk _ _ _ _ (inv E₁)
  let δ₂ := TwoSquare.mk _ _ _ _ (inv E₂)
  have h : TwoSquare.mk _ _ _ _ (inv E₃) =
      ((δ₁.hComp δ₂).whiskerTop c'.hom).whiskerBottom c.inv := by
    apply TwoSquare.ext
    intro M
    dsimp only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop, TwoSquare.hComp,
      TwoSquare.mk, TwoSquare.natTrans, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app]
    simp only [Category.id_comp, Category.comp_id, Category.assoc]
    let Vw := (upperStar (ModuleCat.{u + 1} A) w).leftDerivedFunctor
    let F := rightDerivedLowerShriek (ModuleCat.{u + 1} A) f''
    have he : (asIso E₃).app M =
        c.app _ ≪≫ Vw.mapIso ((asIso E₁).app M) ≪≫
          (asIso E₂).app _ ≪≫ F.mapIso (c'.symm.app M) := by
      apply Iso.ext
      apply (cancel_epi (c.inv.app _)).mp
      apply (cancel_mono (F.map (c'.hom.app M))).mp
      simp only [Iso.app_hom, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
        asIso_hom, Category.assoc, Iso.inv_hom_id_app_assoc,
        ← F.map_comp, Iso.inv_hom_id_app]
      have hid := CategoryTheory.Functor.map_id F
        (((upperStar (ModuleCat.{u + 1} A) v').leftDerivedFunctor ⋙
          (upperStar (ModuleCat.{u + 1} A) w').leftDerivedFunctor).obj M)
      rw [hid]
      erw [Category.comp_id]
      exact (exchange_paste A sq₁ sq₂ M).symm
    have hi := congrArg Iso.inv he
    simpa only [Iso.app_inv, asIso_inv, Iso.trans_inv, Functor.mapIso_inv,
      Iso.symm_inv, Category.assoc, Vw, F] using hi
  have hm := congrArg (fun z ↦ z.natTrans.app K)
    (congrArg (mateEquiv
      (rightDerivedUpperShriekAdjunction A f)
      (rightDerivedUpperShriekAdjunction A f'')) h)
  rw [mateEquiv_whiskerTop_whiskerBottom, mateEquiv_vcomp] at hm
  simpa only [rightDerivedUpperShriekBaseChangeMap, δ₁, δ₂, E₁, E₂, E₃,
    TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
    TwoSquare.natTrans, TwoSquare.mk, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc, c, c'] using hm

private noncomputable abbrev unit_dualizing
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :=
  (rightDerivedUpperShriek A f).obj (ordinaryFiniteUnit A Y)

private noncomputable def unit_base_change
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {v : Y' ⟶ Y} {v' : X' ⟶ X}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback v' f' f v) :=
  (rightDerivedUpperShriekBaseChangeMap A sq).app (ordinaryFiniteUnit A Y) ≫
    (rightDerivedUpperShriek A f').map (ordinaryFiniteUnitPullback A v).hom

private theorem dualizing_base_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v' : X' ⟶ X} {w' : X'' ⟶ X'}
    [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f'] [QuasiCompact f'']
    (sq₁ : IsPullback v' f' f v) (sq₂ : IsPullback w' f'' f' w) :
    unit_base_change A (sq₂.paste_horiz sq₁) =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v').hom.app
        (unit_dualizing A f) ≫
      (upperStar (ModuleCat.{u + 1} A) w').leftDerivedFunctor.map
        (unit_base_change A sq₁) ≫ unit_base_change A sq₂ := by
  have hu := ordinaryFiniteUnitPullback_comp A w v (w ≫ v) rfl
  have hn := (rightDerivedUpperShriekBaseChangeMap A sq₂).naturality
    (ordinaryFiniteUnitPullback A v).hom
  simp only [Functor.comp_map] at hn
  unfold unit_base_change unit_dualizing
  rw [exceptional_base_comp A sq₁ sq₂]
  simp only [Category.assoc, Functor.map_comp]
  erw [reassoc_of% hn]
  rw [← hu]
  simp only [Functor.map_comp]
  simp only [← Functor.map_comp, Iso.inv_hom_id_app_assoc]
  rfl

private theorem section_pullback_comp
    (A : Type (u + 1)) [CommRing A]
    {B B' B'' X X' X'' : Scheme.{u}}
    (v : B' ⟶ B) (w : B'' ⟶ B')
    (s : B ⟶ X) (s' : B' ⟶ X') (s'' : B'' ⟶ X'')
    (r : X' ⟶ X) (r' : X'' ⟶ X')
    (h₁ : v ≫ s = s' ≫ r) (h₂ : w ≫ s' = s'' ≫ r')
    (h₃ : (w ≫ v) ≫ s = s'' ≫ (r' ≫ r)) (K : DerivedCategoryModule A X) :
    (bundleSectionPullbackSquare A s s'' (r' ≫ r) (w ≫ v) h₃.symm K).hom ≫
        (upperStar (ModuleCat.{u + 1} A) s'').leftDerivedFunctor.map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r' r).hom.app K) =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w v).hom.app
        ((upperStar (ModuleCat.{u + 1} A) s).leftDerivedFunctor.obj K) ≫
      (upperStar (ModuleCat.{u + 1} A) w).leftDerivedFunctor.map
        (bundleSectionPullbackSquare A s s' r v h₁.symm K).hom ≫
      (bundleSectionPullbackSquare A s' s'' r' w h₂.symm
        ((upperStar (ModuleCat.{u + 1} A) r).leftDerivedFunctor.obj K)).hom := by
  let C := ModuleCat.{u + 1} A
  have ha := leftDerivedUpperStarComp_assoc'_app C w v s (w ≫ v) (v ≫ s)
    ((w ≫ v) ≫ s) rfl rfl rfl K
  have hb := leftDerivedUpperStarComp_assoc'_app C w s' r (w ≫ s') (v ≫ s)
    ((w ≫ v) ≫ s) rfl h₁ (by rw [Category.assoc, h₁, Category.assoc]) K
  have hc := leftDerivedUpperStarComp_assoc'_app C s'' r' r (w ≫ s') (r' ≫ r)
    ((w ≫ v) ≫ s) h₂ rfl (by rw [Category.assoc, h₁, Category.assoc]) K
  unfold bundleSectionPullbackSquare
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.map_comp, Category.assoc]
  apply (cancel_epi ((leftDerivedUpperStarComp C (w ≫ v) s).hom.app K)).mp
  dsimp only [C] at ha hb hc ⊢
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← reassoc_of% ha]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rw [reassoc_of% hb, Iso.hom_inv_id_app_assoc]
  exact hc

-- The explicit composite arrow avoids rewriting a dependent hom type in the specialization.
private theorem comparison_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' B B' B'' : Scheme.{u}}
    (f : X ⟶ B) (f' : X' ⟶ B') (f'' : X'' ⟶ B'')
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f] [QuasiCompact f'] [QuasiCompact f'']
    {a : X' ⟶ X} {a' : X'' ⟶ X'} {v : B' ⟶ B} {v' : B'' ⟶ B'}
    (sq : IsPullback a f' f v) (sq' : IsPullback a' f'' f' v')
    (s : B ⟶ X) (s' : B' ⟶ X') (s'' : B'' ⟶ X'')
    (hs : s' ≫ a = v ≫ s) (hs' : s'' ≫ a' = v' ≫ s')
    (vv : B'' ⟶ B) (hvv : vv = v' ≫ v) (sq'' : IsPullback (a' ≫ a) f'' f vv)
    (hss : s'' ≫ (a' ≫ a) = vv ≫ s) :
    bundleSectionComparison A f f'' (a' ≫ a) vv sq'' s s'' hss =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v' v vv hvv).hom.app
          ((ordinaryFinitePullback A s).obj (unit_dualizing A f)) ≫
        (ordinaryFinitePullback A v').map
          (bundleSectionComparison A f f' a v sq s s' hs) ≫
        bundleSectionComparison A f' f'' a' v' sq' s' s'' hs' := by
  subst vv
  have hd := dualizing_base_comp A sq sq'
  have hp := section_pullback_comp A v v' s s' s'' a a' hs.symm hs'.symm
    (by rw [Category.assoc, ← hs, ← Category.assoc, ← hs', Category.assoc])
    (unit_dualizing A f)
  change (bundleSectionPullbackSquare A s s'' (a' ≫ a) (v' ≫ v) _
    (unit_dualizing A f)).hom ≫
    (ordinaryFinitePullback A s'').map (unit_base_change A (sq'.paste_horiz sq)) = _
  rw [hd]
  simp only [Functor.map_comp]
  erw [reassoc_of% hp]
  have hn := ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v' s').symm ≪≫
    leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s'' a' (v' ≫ s') hs'.symm).hom.naturality
      (unit_base_change A sq)
  simp only [Functor.comp_map, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc] at hn
  change _ = _ at hn
  simp only [bundleSectionPullbackSquare, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.map_comp, Category.assoc]
  erw [← reassoc_of% hn]
  simp only [bundleSectionComparison, bundleSectionPullbackSquare,
    unit_base_change, unit_dualizing, Functor.map_comp, Category.assoc,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom]
  rfl

end AlgebraicGeometry.Etale
