/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.P1.P1KummerScalarEndpoints
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.ProperBaseChange.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.SmoothPurity.FiniteEtaleTateLinePullback
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.SmoothPurity.EtaleFiniteTwistPullbackRest
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryComparison
public import WeilConjectures.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
public import WeilConjectures.SmoothPurity.FiniteP1ChernMapBaseChange
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth

import WeilConjectures.AlgebraicGeometry.P1.P1KummerChernScalarClassTransport
import WeilConjectures.AlgebraicGeometry.P1.P1KummerChernScalar
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
import WeilConjectures.SixFunctors.BaseChange.RestrictScalars
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMate
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackComposition
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import all WeilConjectures.SmoothPurity.FiniteEtaleTateLinePullback


/-!
# Finite-ring coefficient comparison preserves the normalized projective-line splitting

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts paragraph (blueprint:
lem-sp-finite-p1-coefficient-splitting).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify

open scoped CategoryTheory.Functor
open CategoryTheory.Abelian

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local implicit_reducible] ordinaryFiniteSingleFunctor ordinaryFiniteDegreeZero

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.mapDerivedCategory Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  upperStar

-- The canonical single-degree comparisons carry an exact sheaf square to degree zero.
private theorem exact_square_single
    {V₀ V₁ W₀ W₁ : Type*} [Category V₀] [Category V₁] [Category W₀] [Category W₁]
    [Abelian V₀] [Abelian V₁] [Abelian W₀] [Abelian W₁]
    [HasDerivedCategory V₀] [HasDerivedCategory V₁]
    [HasDerivedCategory W₀] [HasDerivedCategory W₁]
    (F : V₀ ⥤ V₁) (G : W₀ ⥤ W₁) (R₀ : W₀ ⥤ V₀) (R₁ : W₁ ⥤ V₁)
    [F.Additive] [G.Additive] [R₀.Additive] [R₁.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits R₀] [PreservesFiniteColimits R₀]
    [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
    (δ : R₀ ⋙ F ≅ G ⋙ R₁) (Y : W₀) :
    F.mapDerivedCategory.map ((R₀.mapDerivedCategorySingleFunctor 0).inv.app Y) ≫
        (Functor.mapDerivedCategorySquareIso δ).hom.app
          ((DerivedCategory.singleFunctor W₀ 0).obj Y) ≫
        R₁.mapDerivedCategory.map ((G.mapDerivedCategorySingleFunctor 0).hom.app Y) ≫
        (R₁.mapDerivedCategorySingleFunctor 0).hom.app (G.obj Y) =
      (F.mapDerivedCategorySingleFunctor 0).hom.app (R₀.obj Y) ≫
        (DerivedCategory.singleFunctor V₁ 0).map (δ.hom.app Y) := by
  dsimp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  simp only [Category.assoc]
  rw [Functor.mapDerivedCategoryNatIso_comp_hom_app_singleFunctor]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor R₀ F Y]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

private theorem exact_insertion_square
    {V₀ V₁ W₀ W₁ : Type*} [Category V₀] [Category V₁] [Category W₀] [Category W₁]
    [Abelian V₀] [Abelian V₁] [Abelian W₀] [Abelian W₁]
    [HasDerivedCategory V₀] [HasDerivedCategory V₁]
    [HasDerivedCategory W₀] [HasDerivedCategory W₁]
    (F : V₀ ⥤ V₁) (G : W₀ ⥤ W₁) (R₀ : W₀ ⥤ V₀) (R₁ : W₁ ⥤ V₁)
    [F.Additive] [G.Additive] [R₀.Additive] [R₁.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits R₀] [PreservesFiniteColimits R₀]
    [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
    (δ : R₀ ⋙ F ≅ G ⋙ R₁)
    {X₀ : V₀} {X₁ : V₁} {Y₀ : W₀} {Y₁ : W₁}
    (η₀ : X₀ ⟶ R₀.obj Y₀) (η₁ : X₁ ⟶ R₁.obj Y₁)
    (p : F.obj X₀ ⟶ X₁) (q : G.obj Y₀ ⟶ Y₁)
    (h : F.map η₀ ≫ δ.hom.app Y₀ ≫ R₁.map q = p ≫ η₁) :
    F.mapDerivedCategory.map ((DerivedCategory.singleFunctor V₀ 0).map η₀ ≫
        (R₀.mapDerivedCategorySingleFunctor 0).inv.app Y₀) ≫
        (Functor.mapDerivedCategorySquareIso δ).hom.app
          ((DerivedCategory.singleFunctor W₀ 0).obj Y₀) ≫
        R₁.mapDerivedCategory.map ((G.mapDerivedCategorySingleFunctor 0).hom.app Y₀ ≫
          (DerivedCategory.singleFunctor W₁ 0).map q) =
      ((F.mapDerivedCategorySingleFunctor 0).hom.app X₀ ≫
        (DerivedCategory.singleFunctor V₁ 0).map p) ≫
        (DerivedCategory.singleFunctor V₁ 0).map η₁ ≫
        (R₁.mapDerivedCategorySingleFunctor 0).inv.app Y₁ := by
  apply (cancel_mono ((R₁.mapDerivedCategorySingleFunctor 0).hom.app Y₁)).mp
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app]
  have hn := (R₁.mapDerivedCategorySingleFunctor 0).hom.naturality q
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  rw [reassoc_of% (exact_square_single F G R₀ R₁ δ Y₀)]
  have hm := (F.mapDerivedCategorySingleFunctor 0).hom.naturality η₀
  dsimp only [Functor.comp_map] at hm
  rw [reassoc_of% hm]
  simp only [← Functor.map_comp]
  rw [h]
  simp only [Functor.map_comp]
  exact congrArg
    (fun z ↦ (F.mapDerivedCategorySingleFunctor 0).hom.app X₀ ≫
      (DerivedCategory.singleFunctor V₁ 0).map p ≫ z)
    (Category.comp_id ((DerivedCategory.singleFunctor V₁ 0).map η₁)).symm

private theorem scalar_endpoint_square
    {C₀ C₁ D₀ D₁ : Type*} [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    {E₀ : C₀ ⥤ D₀} {E₁ : C₁ ⥤ D₁} {U₀ : D₀ ⥤ C₀} {U₁ : D₁ ⥤ C₁}
    (a₀ : E₀ ⊣ U₀) (a₁ : E₁ ⊣ U₁) (F : C₀ ⥤ C₁) (G : D₀ ⥤ D₁)
    (δ : U₀ ⋙ F ⟶ G ⋙ U₁) (r : F ⋙ E₁ ⟶ E₀ ⋙ G)
    (hr : ∀ X, a₁.unit.app (F.obj X) ≫ U₁.map (r.app X) =
      F.map (a₀.unit.app X) ≫ δ.app (E₀.obj X))
    {X₀ : C₀} {X₁ : C₁} {Y₀ : D₀} {Y₁ : D₁}
    (e₀ : E₀.obj X₀ ⟶ Y₀) (e₁ : E₁.obj X₁ ⟶ Y₁)
    (p : F.obj X₀ ⟶ X₁) (q : G.obj Y₀ ⟶ Y₁)
    (h : F.map (a₀.homEquiv _ _ e₀) ≫ δ.app Y₀ ≫ U₁.map q =
      p ≫ a₁.homEquiv _ _ e₁) :
    r.app X₀ ≫ G.map e₀ ≫ q = E₁.map p ≫ e₁ := by
  apply (a₁.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [reassoc_of% (hr X₀)]
  have hn := δ.naturality e₀
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn, ← F.map_comp_assoc]
  have hp := a₁.unit.naturality p
  dsimp only [Functor.id_map, Functor.comp_map] at hp
  rw [← reassoc_of% hp]
  simpa only [Adjunction.homEquiv_unit] using h

-- Ordinary endpoint squares are checked after the geometric adjunction.
private theorem restriction_pullback_adjunct
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)}
    {P : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)}
    (g : (upperStar (ModuleCat.{u + 1} B) f).obj M ⟶ P) :
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _
        ((upperStarRestrictScalarsIsoSheaf φ f).hom.app M ≫
          (Sheaf.restrictScalars X.smallEtaleTopology φ).map g) =
      (Sheaf.restrictScalars Y.smallEtaleTopology φ).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).homEquiv _ _ g) ≫
        (lowerStarCompRestrictScalarsIso φ f).hom.app P := by
  rw [← restrictionIso_eq]
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  have hu := restrictScalars_map_unit_app φ f M
  change (Sheaf.restrictScalars Y.smallEtaleTopology φ).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).unit.app M) =
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).unit.app _ ≫
      (lowerStar (ModuleCat.{u + 1} A) f).map
        ((upperStarRestrictScalarsIso φ f).hom.app M) at hu
  rw [← hu]
  rfl

private theorem line_insertion_pullback
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {φ : A →+* B} {N : ℕ} {hA : (N : A) = 0} {hB : (N : B) = 0}
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤)))
    (eY : P1KummerScalarEndpoints φ N hA hB Y)
    (eX : P1KummerScalarEndpoints φ N hA hB X)
    (tA : OrdinaryFiniteTwistTransport A N hA)
    (tB : OrdinaryFiniteTwistTransport B N hB) :
    (upperStar (ModuleCat.{u + 1} A) f).map eY.lineInsertion ≫
        (upperStarRestrictScalarsIsoSheaf φ f).hom.app _ ≫
        (Sheaf.restrictScalars X.smallEtaleTopology φ).map (tB.line f hY).hom =
      (tA.line f hY).hom ≫ eX.lineInsertion := by
  have hr : (tA.roots f hY).hom = (tB.roots f hY).hom := by
    apply (cancel_mono (kernel.ι (N • 𝟙 X.gmSheaf))).mp
    exact (tA.roots_normalization f hY).symm.trans (tB.roots_normalization f hY)
  apply ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, restriction_pullback_adjunct,
    Adjunction.homEquiv_naturality_right]
  apply (Scheme.lineHomEquiv Y N A hA _).injective
  ext W z
  simp only [Scheme.lineHomEquiv_generator]
  change (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).homEquiv _ _
      (tB.line f hY).hom).hom.app W)
      (eY.lineInsertion.hom.app W
        (Scheme.finiteEtaleTateOneGenerator A N Y hA W 1 z)) =
    eX.lineInsertion.hom.app
      ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).op.obj W)
      ((((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _
        (tA.line f hY).hom).hom.app W)
          (Scheme.finiteEtaleTateOneGenerator A N Y hA W 1 z))
  rw [eY.line_normalization, tB.line_normalization, tA.line_normalization,
    eX.line_normalization, hr]

private theorem unit_insertion_pullback
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {φ : A →+* B} {N : ℕ} {hA : (N : A) = 0} {hB : (N : B) = 0}
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (eY : P1KummerScalarEndpoints φ N hA hB Y)
    (eX : P1KummerScalarEndpoints φ N hA hB X) :
    (upperStar (ModuleCat.{u + 1} A) f).map eY.unitInsertion ≫
        (upperStarRestrictScalarsIsoSheaf φ f).hom.app _ ≫
        (Sheaf.restrictScalars X.smallEtaleTopology φ).map
          ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} B) f).app
            (ModuleCat.of B B)).hom =
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).app
        (ModuleCat.of A A)).hom ≫ eX.unitInsertion := by
  apply ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, restriction_pullback_adjunct,
    Adjunction.homEquiv_naturality_right]
  rw [← Category.assoc]
  apply (Iso.eq_comp_inv
    ((lowerStarCompRestrictScalarsIso φ f).app (ordinaryFiniteConstant B X))).mp
  simpa only [supportedConstantUnit, Iso.app_inv, Functor.comp_obj,
    ordinaryFiniteConstant, Category.assoc] using
    supported_kummer_scalar_units_commute φ f eX.unitInsertion eY.unitInsertion
      eX.unit_normalization eY.unit_normalization

private theorem derived_insertion_pullback
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {M' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)}
    {P : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {P' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)}
    (ηY : M ⟶ (Sheaf.restrictScalars Y.smallEtaleTopology φ).obj M')
    (ηX : P ⟶ (Sheaf.restrictScalars X.smallEtaleTopology φ).obj P')
    (eY : (scalarExtension φ Y).obj ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj M')
    (eX : (scalarExtension φ X).obj ((DerivedCategory.singleFunctor _ 0).obj P) ≅
      (DerivedCategory.singleFunctor _ 0).obj P')
    (heY : eY.hom = p1KummerDerivedInsertion φ Y ηY)
    (heX : eX.hom = p1KummerDerivedInsertion φ X ηX)
    (p : (upperStar (ModuleCat.{u + 1} A) f).obj M ⟶ P)
    (q : (upperStar (ModuleCat.{u + 1} B) f).obj M' ⟶ P')
    (h : (upperStar (ModuleCat.{u + 1} A) f).map ηY ≫
      (upperStarRestrictScalarsIsoSheaf φ f).hom.app M' ≫
      (Sheaf.restrictScalars X.smallEtaleTopology φ).map q = p ≫ ηX) :
    (scalarExactIso φ f).inv.app ((DerivedCategory.singleFunctor _ 0).obj M) ≫
        (upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory.map eY.hom ≫
        ((upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategorySingleFunctor 0).hom.app M' ≫
        (DerivedCategory.singleFunctor _ 0).map q =
      (scalarExtension φ X).map
        (((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategorySingleFunctor 0).hom.app M ≫
          (DerivedCategory.singleFunctor _ 0).map p) ≫ eX.hom := by
  apply scalar_endpoint_square
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ))
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory
    (restrictionExactIso φ f).hom (scalarExactIso φ f).inv
    (scalarExact_inverse_unit φ f) eY.hom eX.hom
    (((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategorySingleFunctor 0).hom.app M ≫
      (DerivedCategory.singleFunctor _ 0).map p)
    (((upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategorySingleFunctor 0).hom.app M' ≫
      (DerivedCategory.singleFunctor _ 0).map q)
  rw [heY, heX]
  simp only [p1KummerDerivedInsertion, SheafExactDegreeZero.scalarAdjointInsertion,
    SheafExactDegreeZero.adjointInsertion, Equiv.apply_symm_apply]
  exact exact_insertion_square _ _ _ _ (upperStarRestrictScalarsIsoSheaf φ f) ηY ηX p q h

-- Transport from exact derived inverse image to the recorded left derived functor.
private theorem insertion_pullback
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {M' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)}
    {P : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {P' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)}
    (ηY : M ⟶ (Sheaf.restrictScalars Y.smallEtaleTopology φ).obj M')
    (ηX : P ⟶ (Sheaf.restrictScalars X.smallEtaleTopology φ).obj P')
    (eY : (scalarExtension φ Y).obj ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj M')
    (eX : (scalarExtension φ X).obj ((DerivedCategory.singleFunctor _ 0).obj P) ≅
      (DerivedCategory.singleFunctor _ 0).obj P')
    (heY : eY.hom = p1KummerDerivedInsertion φ Y ηY)
    (heX : eX.hom = p1KummerDerivedInsertion φ X ηX)
    (p : (upperStar (ModuleCat.{u + 1} A) f).obj M ⟶ P)
    (q : (upperStar (ModuleCat.{u + 1} B) f).obj M' ⟶ P')
    (h : (upperStar (ModuleCat.{u + 1} A) f).map ηY ≫
      (upperStarRestrictScalarsIsoSheaf φ f).hom.app M' ≫
      (Sheaf.restrictScalars X.smallEtaleTopology φ).map q = p ≫ ηX) :
    (scalarPullbackIso φ f).hom.app ((DerivedCategory.singleFunctor _ 0).obj M) ≫
        (scalarExtension φ X).map
          ((ordinaryFiniteSinglePullbackIso A f).hom.app M ≫
            (DerivedCategory.singleFunctor _ 0).map p) ≫ eX.hom =
      (ordinaryFinitePullback B f).map eY.hom ≫
        (ordinaryFiniteSinglePullbackIso B f).hom.app M' ≫
        (DerivedCategory.singleFunctor _ 0).map q := by
  have hh := derived_insertion_pullback φ f ηY ηX eY eX heY heX p q h
  have hh' := congrArg
    ((scalarExtension φ X).map
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj M)) ≫ ·) hh
  dsimp only [scalarExactIso, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app] at hh'
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.assoc] at hh'
  have hn := (leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} B) f).hom.naturality eY.hom
  rw [← reassoc_of% hn] at hh'
  apply (cancel_epi ((scalarPullbackIso φ f).inv.app
    ((DerivedCategory.singleFunctor _ 0).obj M))).mp
  simpa only [Iso.inv_hom_id_app_assoc, ordinaryFiniteSinglePullbackIso,
    ordinaryFiniteSingleExactPullbackIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.map_comp,
    ordinaryFiniteSingleFunctor_eq, ordinaryFinitePullback, Category.assoc] using hh'.symm

private theorem unit_pullback_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {φ : A →+* B} {N : ℕ} {hA : (N : A) = 0} {hB : (N : B) = 0}
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (eY : P1KummerScalarEndpoints φ N hA hB Y)
    (eX : P1KummerScalarEndpoints φ N hA hB X) :
    (scalarPullbackIso φ f).hom.app (ordinaryFiniteUnit A Y) ≫
        (scalarExtension φ X).map (ordinaryFiniteUnitPullback A f).hom ≫ eX.unitIso.hom =
      (ordinaryFinitePullback B f).map eY.unitIso.hom ≫
        (ordinaryFiniteUnitPullback B f).hom := by
  exact insertion_pullback φ f eY.unitInsertion eX.unitInsertion eY.unitIso eX.unitIso
    eY.unit_derived eX.unit_derived _ _ (unit_insertion_pullback f eY eX)

private theorem line_pullback_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {φ : A →+* B} {N : ℕ} {hA : (N : A) = 0} {hB : (N : B) = 0}
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤)))
    (eY : P1KummerScalarEndpoints φ N hA hB Y)
    (eX : P1KummerScalarEndpoints φ N hA hB X)
    (tA : OrdinaryFiniteTwistTransport A N hA)
    (tB : OrdinaryFiniteTwistTransport B N hB) :
    (scalarPullbackIso φ f).hom.app (ordinaryFiniteLine A N hA Y) ≫
        (scalarExtension φ X).map
          ((ordinaryFiniteSinglePullbackIso A f).hom.app _ ≫
            (ordinaryFiniteSingleFunctor A X).map (tA.line f hY).hom) ≫ eX.lineIso.hom =
      (ordinaryFinitePullback B f).map eY.lineIso.hom ≫
        (ordinaryFiniteSinglePullbackIso B f).hom.app _ ≫
          (ordinaryFiniteSingleFunctor B X).map (tB.line f hY).hom := by
  exact insertion_pullback φ f eY.lineInsertion eX.lineInsertion eY.lineIso eX.lineIso
    eY.line_derived eX.line_derived _ _ (line_insertion_pullback f hY eY eX tA tB)

attribute [local instance] scalar_commShift pullback_commShift

private theorem scalar_restriction_shift
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (scalarRestrictionPullbackIso φ f).hom.CommShift ℤ := by
  dsimp only [scalarRestrictionPullbackIso, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom,
    Functor.mapDerivedCategorySquareIso]
  infer_instance

private theorem inverse_mate_shift
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ] [HasShift F ℤ]
    {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    [G.CommShift ℤ] [H.CommShift ℤ] [L₁.CommShift ℤ] [R₁.CommShift ℤ]
    [L₂.CommShift ℤ] [R₂.CommShift ℤ]
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) [adj₁.CommShift ℤ] [adj₂.CommShift ℤ]
    (β : TwoSquare R₁ H G R₂) [β.natTrans.CommShift ℤ] :
    ((mateEquiv adj₁ adj₂).symm β).natTrans.CommShift ℤ := by
  change ((Functor.leftUnitor (G ⋙ L₂)).inv ≫
    Functor.whiskerRight adj₁.unit (G ⋙ L₂) ≫
    (Functor.associator (L₁ ⋙ R₁) G L₂).inv ≫
    Functor.whiskerRight (Functor.associator L₁ R₁ G).hom L₂ ≫
    Functor.whiskerRight (Functor.whiskerLeft L₁ β.natTrans) L₂ ≫
    Functor.whiskerRight (Functor.associator L₁ H R₂).inv L₂ ≫
    (Functor.associator (L₁ ⋙ H) R₂ L₂).hom ≫
    Functor.whiskerLeft (L₁ ⋙ H) adj₂.counit ≫
    (Functor.rightUnitor (L₁ ⋙ H)).hom).CommShift ℤ
  infer_instance

private theorem scalar_pullback_shift
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (scalarPullbackIso φ f).hom.CommShift ℤ := by
  let : (ordinaryFinitePullback A f).CommShift ℤ :=
    commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} A) f
  let : (ordinaryFinitePullback B f).CommShift ℤ :=
    commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} B) f
  let := (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ)).leftAdjointCommShift ℤ
  let := (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)).leftAdjointCommShift ℤ
  let := (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ)).commShift_of_rightAdjoint ℤ
  let := (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)).commShift_of_rightAdjoint ℤ
  let := scalar_restriction_shift φ f
  rw [← scalarPullback_eq]
  dsimp only [ProEtale.scalarPullbackEtaleIsoFromMate, Iso.symm_hom, asIso_inv]
  have h : (ProEtale.scalarPullbackReverseEtale φ f).CommShift ℤ := by
    exact inverse_mate_shift _ _ _
  let := (ProEtale.scalarPullbackReverse_isIso φ f).2
  exact NatTrans.CommShift.of_isIso _ ℤ

private theorem shifted_cube
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    [HasShift C ℤ] [HasShift D ℤ] [HasShift C' ℤ] [HasShift D' ℤ]
    (F : C ⥤ C') (Q : C ⥤ D) (R : C' ⥤ D') (G : D ⥤ D')
    [F.CommShift ℤ] [Q.CommShift ℤ] [R.CommShift ℤ] [G.CommShift ℤ]
    (e : F ⋙ R ≅ Q ⋙ G) {E : C} {L : C'} {M : D} {N : D'}
    (s : F.obj E ⟶ L) (a : R.obj L ⟶ N) (p : Q.obj E ⟶ M) (t : G.obj M ⟶ N)
    (r : ℤ)
    (hcube : R.map s ≫ a = e.hom.app E ≫ G.map p ≫ t)
    (hshift : R.map ((F.commShiftIso r).hom.app E) ≫
      (R.commShiftIso r).hom.app (F.obj E) ≫ (e.hom.app E)⟦r⟧' =
      e.hom.app (E⟦r⟧) ≫ G.map ((Q.commShiftIso r).hom.app E) ≫
        (G.commShiftIso r).hom.app (Q.obj E)) :
    R.map ((F.commShiftIso r).hom.app E) ≫ R.map (s⟦r⟧') ≫
      (R.commShiftIso r).hom.app L ≫ a⟦r⟧' =
    e.hom.app (E⟦r⟧) ≫ G.map ((Q.commShiftIso r).hom.app E ≫ p⟦r⟧') ≫
      (G.commShiftIso r).hom.app M ≫ t⟦r⟧' := by
  calc
    _ = R.map ((F.commShiftIso r).hom.app E) ≫
        (R.commShiftIso r).hom.app (F.obj E) ≫ (R.map s ≫ a)⟦r⟧' := by
      simp only [Functor.map_comp]
      rw [Functor.commShiftIso_hom_naturality_assoc]
    _ = R.map ((F.commShiftIso r).hom.app E) ≫
        (R.commShiftIso r).hom.app (F.obj E) ≫
          (e.hom.app E ≫ G.map p ≫ t)⟦r⟧' := by rw [hcube]
    _ = (R.map ((F.commShiftIso r).hom.app E) ≫
        (R.commShiftIso r).hom.app (F.obj E) ≫ (e.hom.app E)⟦r⟧') ≫
          (G.map p)⟦r⟧' ≫ t⟦r⟧' := by
      simp only [Functor.map_comp]
      simp only [Category.assoc]
    _ = _ := by
      rw [hshift]
      simp only [Functor.map_comp, Category.assoc]
      rw [Functor.commShiftIso_hom_naturality_assoc]

-- Shift the normalized line square with precisely the endpoint shift structures.
private theorem shifted_line_pullback_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {φ : A →+* B} {N : ℕ} {hA : (N : A) = 0} {hB : (N : B) = 0}
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤)))
    (eY : P1KummerScalarEndpoints φ N hA hB Y)
    (eX : P1KummerScalarEndpoints φ N hA hB X)
    (tA : OrdinaryFiniteTwistTransport A N hA)
    (tB : OrdinaryFiniteTwistTransport B N hB) :
    (scalarPullbackIso φ f).hom.app ((ordinaryFiniteLine A N hA Y)⟦(2 : ℤ)⟧) ≫
        (scalarExtension φ X).map (ordinaryFiniteShiftedLinePullback A N hA tA f hY).hom ≫
        eX.shiftedLineIso.hom =
      (ordinaryFinitePullback B f).map eY.shiftedLineIso.hom ≫
        (ordinaryFiniteShiftedLinePullback B N hB tB f hY).hom := by
  let : (ordinaryFinitePullback A f).CommShift ℤ :=
    commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} A) f
  let : (ordinaryFinitePullback B f).CommShift ℤ :=
    commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} B) f
  let := (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ)).leftAdjointCommShift ℤ
  let := (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)).leftAdjointCommShift ℤ
  let := scalar_pullback_shift φ f
  have hc := line_pullback_square f hY eY eX tA tB
  have hs := NatTrans.shift_app_comm (scalarPullbackIso φ f).hom (2 : ℤ)
    (ordinaryFiniteLine A N hA Y)
  simp only [Functor.commShiftIso_comp_hom_app] at hs
  have hh := shifted_cube (scalarExtension φ Y) (ordinaryFinitePullback A f)
    (ordinaryFinitePullback B f) (scalarExtension φ X) (scalarPullbackIso φ f)
    eY.lineIso.hom
    ((ordinaryFiniteSinglePullbackIso B f).hom.app _ ≫
      (ordinaryFiniteSingleFunctor B X).map (tB.line f hY).hom)
    ((ordinaryFiniteSinglePullbackIso A f).hom.app _ ≫
      (ordinaryFiniteSingleFunctor A X).map (tA.line f hY).hom)
    eX.lineIso.hom 2 hc.symm (by
      simpa only [ordinaryFinitePullback, Category.assoc] using hs)
  have hx : (scalarExtension φ X).commShiftIso (2 : ℤ) =
      Adjunction.LeftAdjointCommShift.iso
        (Adjunction.ofIsRightAdjoint
          (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)) (2 : ℤ) := rfl
  have hy : (scalarExtension φ Y).commShiftIso (2 : ℤ) =
      Adjunction.LeftAdjointCommShift.iso
        (Adjunction.ofIsRightAdjoint
          (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ)) (2 : ℤ) := rfl
  simpa only [ordinaryFiniteShiftedLinePullback_eq, P1KummerScalarEndpoints.shiftedLineIso,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc, hx, hy, ordinaryFiniteLine, ordinaryFiniteSingleFunctor_eq,
    ordinaryFiniteDegreeZero, ordinaryFinitePullback] using hh.symm

-- A geometric mate sends compatible adjoints to compatible pushforward columns.
private theorem geometric_mate_column
    {C₀ C₁ D₀ D₁ : Type*} [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    {F₀ : C₀ ⥤ D₀} {F₁ : C₁ ⥤ D₁} {H₀ : D₀ ⥤ C₀} {H₁ : D₁ ⥤ C₁}
    (a₀ : F₀ ⊣ H₀) (a₁ : F₁ ⊣ H₁) (T : C₀ ⥤ C₁) (E : D₀ ⥤ D₁)
    (κ : T ⋙ F₁ ⟶ F₀ ⋙ E)
    {K : C₀} {K' : C₁} {L : D₀} {L' : D₁}
    (f : F₀.obj K ⟶ L) (g : F₁.obj K' ⟶ L')
    (e : E.obj L ⟶ L') (u : T.obj K ⟶ K')
    (h : κ.app K ≫ E.map f ≫ e = F₁.map u ≫ g) :
    T.map (a₀.homEquiv _ _ f) ≫
        (mateEquiv a₀ a₁ (TwoSquare.mk _ _ _ _ κ)).natTrans.app L ≫ H₁.map e =
      u ≫ a₁.homEquiv _ _ g := by
  apply (a₁.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have he := a₁.counit.naturality e
  dsimp only [Functor.comp_map, Functor.id_map] at he
  rw [he]
  rw [reassoc_of% (mateEquiv_counit a₀ a₁ (TwoSquare.mk _ _ _ _ κ) L)]
  have hn := κ.naturality (a₀.homEquiv _ _ f)
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, ← E.map_comp_assoc]
  have ht : F₀.map (a₀.homEquiv _ _ f) ≫ a₀.counit.app L = f := by
    simpa only [Adjunction.homEquiv_counit] using (a₀.homEquiv K L).symm_apply_apply f
  rw [ht]
  have ht' : F₁.map (a₁.homEquiv _ _ g) ≫ a₁.counit.app L' = g := by
    simpa only [Adjunction.homEquiv_counit] using (a₁.homEquiv K' L').symm_apply_apply g
  rw [ht']
  exact h

private theorem biproduct_comparison
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] [PreservesBinaryBiproducts F]
    {X Y Z : C} {X' Y' Z' : D}
    (a : X ⟶ Z) (b : Y ⟶ Z) (a' : X' ⟶ Z') (b' : Y' ⟶ Z')
    (x : F.obj X ⟶ X') (y : F.obj Y ⟶ Y') (e : F.obj Z ⟶ Z')
    (ha : F.map a ≫ e = x ≫ a') (hb : F.map b ≫ e = y ≫ b') :
    F.map (biprod.desc a b) ≫ e =
      biprod.lift (F.map biprod.fst ≫ x) (F.map biprod.snd ≫ y) ≫ biprod.desc a' b' := by
  apply (cancel_epi (F.mapBiprod X Y).inv).mp
  apply biprod.hom_ext' <;>
    simp only [Functor.mapBiprod_inv, ← Category.assoc, biprod.inl_desc,
      biprod.inr_desc, ← F.map_comp]
  · rw [ha]
    simp [← Functor.map_comp_assoc]
  · rw [hb]
    simp [← Functor.map_comp_assoc]

private theorem trace_of_splitting
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) {X Y Z : C} {X' Y' Z' : D}
    (a : X ⊞ Y ≅ Z) (b : X' ⊞ Y' ≅ Z')
    (x : F.obj X ⟶ X') (y : F.obj Y ⟶ Y') (e : F.obj Z ⟶ Z')
    (h : F.map a.hom ≫ e =
      biprod.lift (F.map biprod.fst ≫ x) (F.map biprod.snd ≫ y) ≫ b.hom) :
    e ≫ b.inv ≫ biprod.snd = F.map (a.inv ≫ biprod.snd) ≫ y := by
  apply (cancel_epi (F.map a.hom)).mp
  rw [← Category.assoc, ← Category.assoc, h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, biprod.lift_snd]
  rw [← F.map_comp_assoc]
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

-- Class transport and uniqueness avoid choosing any residue-coefficient endpoints.
private theorem firstChern_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {φ : A →+* B} {N : ℕ} {hA : (N : A) = 0} {hB : (N : B) = 0}
    {T : Scheme.{u}} (hT : IsUnit (N : Γ(T, ⊤)))
    (e : P1KummerScalarEndpoints φ N hA hB T) (M : T.Pic) :
    (scalarExtension φ T).map (ordinaryFiniteFirstChern A N hA T hT M) ≫
        e.shiftedLineIso.hom =
      e.unitIso.hom ≫ ordinaryFiniteFirstChern B N hB T hT M := by
  have hroot : ordinaryFiniteRootMap A N hA T ≫ p1KummerScalarForgetLineMap e =
      ordinaryFiniteRootMap B N hB T := by
    ext W z
    change e.lineInsertion.hom.app W
      (Scheme.finiteEtaleTateOneGenerator A N T hA W 1 z) =
        Scheme.finiteEtaleTateOneGenerator B N T hB W 1 z
    simpa only [map_one] using e.line_normalization W 1 z
  have hc : e.chernImage (ordinaryFiniteFirstChern A N hA T hT M) =
      ordinaryFiniteFirstChern B N hB T hT M := by
    apply ordinaryFiniteFirstChern_unique
    rw [p1KummerChernScalar_class_transport, ordinaryFiniteFirstChern_class,
      ← Sheaf.H.map_comp_apply, hroot]
  have hh := congrArg (e.unitIso.hom ≫ ·) hc
  simpa only [P1KummerScalarEndpoints.chernImage, Iso.hom_inv_id_assoc] using hh

/-- The normalized projective-line splitting and its trace commute with arbitrary finite
coefficient extension, and the diagonal Kummer class is carried to the corresponding
coefficient class. The proper comparison is the scalar mate, whose definition is the
counit transpose. The proof is the retained chart calculation in the source.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts paragraph (blueprint:
lem-sp-finite-p1-coefficient-splitting).

Proof:
(1) Ordinary insertion squares. For the constants, transpose along the inverse-image/
direct-image adjunction and use supported_kummer_scalar_units_commute
(lem-asd-supported-kummer-scalar-maps): both paths send a constant a to φ(a). For the Tate
line, transpose and use the generator description of finiteEtaleTateLine
(lem-asd-finite-etale-tate-line-comparison); the root pullback maps of tA and tB agree,
being normalized by the same monomorphism into G_m, so both paths send the generator
(a, z) to (φ(a), f^*z) (def-sp-p1-kummer-scalar-endpoints).
(2) Derived pullback squares. Exact derived inverse image and restriction of scalars carry
these squares to degree zero through the single-degree comparisons. Transposing through the
derived scalar adjunction with the endpoint fields unit_derived and line_derived, and
identifying the inverse scalar/pullback comparison with the scalar-adjunction mate of the
restriction square (lem-sfb-etale-proetale-scalar-mate, lem-sf-scalar-pullback-composition),
transported along L f^* ≅ exact f^*, gives the unit and unshifted Tate pullback squares.
The scalar comparison commutes with shifts (adjunction transposition of the shift
compatibilities of restriction and inverse image); shifting the Tate square by two gives
the shifted Tate pullback square.
(3) Chern arrows. By p1KummerChernScalar (lem-sp-p1-kummer-chern-scalar) the conjugate of
dA.chern has the B Chern class; injectivity of ordinaryFiniteClass
(lem-sp-ordinary-finite-class-arbitrary-base) identifies it with dB.chern, so
T_P(dA.chern) λ_P = u_P dB.chern.
(4) Columns. For an A-adjoint pair the B-adjoint of T_S(adjunct) ≫ scalarMate ≫ H_B(e) is
the scalar image of the A arrow preceded by the scalar/pullback comparison and followed by e
(counit naturality, mateEquiv_counit, naturality of the comparison). Applied to the
shifted Tate pullback and to unit pullback followed by the Chern arrow, steps 2 and 3 give
γ T_S(v_A) = λ_S v_B and γ T_S(h_A) = u_S h_B for the two columns of the decompositions.
(5) Splitting and trace. T_S is a left adjoint, hence additive and preserving binary
biproducts; decomposition_hom and biproduct extensionality give the splitting equality.
Postcomposing with dB.decomposition.inv ≫ snd and cancelling T_S(dA.decomposition.hom)
gives the trace equality, trace being decomposition.inv ≫ snd.
(6) Diagonal. On any T with N invertible and any line bundle M, the line insertion after
the A root map is the B root map (evaluate at the root generator, φ(1) = 1). Class
transport (lem-sp-p1-kummer-chern-class-transport) and uniqueness of ordinaryFiniteFirstChern
(def-sp-ordinary-finite-first-chern) give T(c_1^A(M)) λ_T = u_T c_1^B(M); take
T = P ×_S P and M = O(Δ).
No step uses flatness of A → B or of Z/N → A.
-/
theorem finiteP1CoefficientSplitting
    (N : ℕ) (_hN : 0 < N)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (eS : P1KummerScalarEndpoints φ N hA hB S)
    (eP : P1KummerScalarEndpoints φ N hA hB (ProjectiveLine S))
    (tA : OrdinaryFiniteTwistTransport A N hA)
    (tB : OrdinaryFiniteTwistTransport B N hB)
    (dA : OrdinaryFiniteP1Datum A N hA tA S hS)
    (dB : OrdinaryFiniteP1Datum B N hB tB S hS) :
    ((scalarExtension φ S).map dA.decomposition.hom ≫
        (scalarMate φ (ProjectiveLine S ↘ S)).app
          ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
        (ordinaryFinitePushforward B (ProjectiveLine S ↘ S)).map
          eP.shiftedLineIso.hom =
      biprod.lift
          ((scalarExtension φ S).map biprod.fst ≫ eS.shiftedLineIso.hom)
          ((scalarExtension φ S).map biprod.snd ≫ eS.unitIso.hom) ≫
        dB.decomposition.hom) ∧
      ((scalarMate φ (ProjectiveLine S ↘ S)).app
          ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
        (ordinaryFinitePushforward B (ProjectiveLine S ↘ S)).map
          eP.shiftedLineIso.hom ≫ dB.trace =
      (scalarExtension φ S).map dA.trace ≫ eS.unitIso.hom) ∧
      ∀ (hW : IsUnit (N : Γ(pullback (ProjectiveLine S ↘ S)
          (ProjectiveLine S ↘ S), ⊤)))
        (eW : P1KummerScalarEndpoints φ N hA hB
          (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))),
        (scalarExtension φ (pullback (ProjectiveLine S ↘ S)
            (ProjectiveLine S ↘ S))).map
          (ordinaryFiniteFirstChern A N hA _ hW
            (@Scheme.Pic.ofIsInvertible _
              (Scheme.Modules.dual (pullback.diagonal (ProjectiveLine S ↘ S)).ker.toModules)
              (projectiveLine_diagonal_ker_isInvertible S).isInvertible_dual_toModules)) ≫
          eW.shiftedLineIso.hom =
        eW.unitIso.hom ≫ ordinaryFiniteFirstChern B N hB _ hW
          (@Scheme.Pic.ofIsInvertible _
            (Scheme.Modules.dual (pullback.diagonal (ProjectiveLine S ↘ S)).ker.toModules)
            (projectiveLine_diagonal_ker_isInvertible S).isInvertible_dual_toModules) := by
  let f := ProjectiveLine S ↘ S
  let E := scalarExtension φ S
  let EP := scalarExtension φ (ProjectiveLine S)
  let LA := ordinaryFinitePullback A f
  let LB := ordinaryFinitePullback B f
  let HB := ordinaryFinitePushforward B f
  let κ := scalarPullbackIso φ f
  let γ := (scalarMate φ f).app
    ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
      HB.map eP.shiftedLineIso.hom
  have hchern : EP.map dA.chern ≫ eP.shiftedLineIso.hom =
      eP.unitIso.hom ≫ dB.chern := by
    have ha := p1KummerChernScalar dA.invertible_on_projectiveLine eP dA.chern dA.chern_spec
    have hb := dB.chern_spec
    have he : eP.chernImage dA.chern = dB.chern := by
      apply (ordinaryFiniteClass_bijective_arbitraryBase B (ProjectiveLine S)
        (Scheme.finiteEtaleTateLine (ProjectiveLine S) N B hB) 2).injective
      exact ha.trans hb.symm
    have hh := congrArg (eP.unitIso.hom ≫ ·) he
    simpa only [P1KummerScalarEndpoints.chernImage, Iso.hom_inv_id_assoc] using hh
  have hv : E.map (ordinaryFiniteP1Unit A N hA tA S hS) ≫ γ =
      eS.shiftedLineIso.hom ≫ ordinaryFiniteP1Unit B N hB tB S hS := by
    have hh := geometric_mate_column
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f) E EP κ.hom
      (ordinaryFiniteShiftedLinePullback A N hA tA f hS).hom
      (ordinaryFiniteShiftedLinePullback B N hB tB f hS).hom
      eP.shiftedLineIso.hom eS.shiftedLineIso.hom
      (shifted_line_pullback_square f hS eS eP tA tB)
    simpa only [ordinaryFiniteP1Unit, Adjunction.homEquiv_unit, scalarMate,
      ordinaryFinitePushforward, f, E, EP, κ, γ, HB, Category.assoc] using hh
  have hh : E.map (ordinaryFiniteP1ChernPushforward A N hA S dA.chern) ≫ γ =
      eS.unitIso.hom ≫ ordinaryFiniteP1ChernPushforward B N hB S dB.chern := by
    apply geometric_mate_column
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f) E EP κ.hom
      ((ordinaryFiniteUnitPullback A f).hom ≫ dA.chern)
      ((ordinaryFiniteUnitPullback B f).hom ≫ dB.chern)
      eP.shiftedLineIso.hom eS.unitIso.hom
    simp only [Functor.map_comp, Category.assoc]
    rw [hchern, reassoc_of% (unit_pullback_square f eS eP)]
    rfl
  have : E.Additive := by
    dsimp only [E, scalarExtension, ProEtale.pbcFixedScalarExtension]
    exact (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars S.smallEtaleTopology φ)).left_adjoint_additive
  have : PreservesBinaryBiproducts E :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts E
  have hd : E.map dA.decomposition.hom ≫ γ =
      biprod.lift (E.map biprod.fst ≫ eS.shiftedLineIso.hom)
        (E.map biprod.snd ≫ eS.unitIso.hom) ≫ dB.decomposition.hom := by
    rw [dA.decomposition_hom, dB.decomposition_hom]
    exact biproduct_comparison E _ _ _ _ _ _ _ hv hh
  refine ⟨hd, ?_, ?_⟩
  · simpa only [OrdinaryFiniteP1Datum.trace, γ, HB, f, E, Category.assoc] using
      trace_of_splitting E dA.decomposition dB.decomposition
        eS.shiftedLineIso.hom eS.unitIso.hom γ hd
  · intro hW eW
    exact firstChern_scalar hW eW _

end AlgebraicGeometry.Etale
