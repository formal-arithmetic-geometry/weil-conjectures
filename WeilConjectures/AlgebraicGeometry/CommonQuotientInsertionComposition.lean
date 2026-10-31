/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CommonQuotientPullbackData
import all WeilConjectures.AlgebraicGeometry.RingedCoefficientPullbackComparisonSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
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

/-! # Composition normalization of geometric scalar insertion

Source: Stacks Project, Tag 0D6D.
(blueprint: lem-weil-pbc-common-quotient-insertion-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SemilinearSections (Mod D)
open SheafOfModules.RingedCoefficientProjection
open SheafOfModules.SuccessiveDerivedQuotient (restriction sectionTensor)
namespace SheafOfModules.CommonQuotientPullback

variable {C X : Type c} [Category.{v} C] [Category.{v} X]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} X]
  {J : GrothendieckTopology C} {K : GrothendieckTopology X}
  {uInv : Sheaf J (Type r) ⥤ Sheaf K (Type r)}
  {uPush : Sheaf K (Type r) ⥤ Sheaf J (Type r)} {adj : uInv ⊣ uPush}
  (g : Geometry uInv uPush adj)
  {pY : Scalars.{c, v, r} J} {pX : Scalars.{c, v, r} K}
  (nY : SuccessiveDerivedQuotient.Normalization (J := J) pY)
  (nX : SuccessiveDerivedQuotient.Normalization (J := K) pX)
  {R B : Sheaf J CommRingCat.{r}} (φ : R ⟶ B)
  {B' : Sheaf K CommRingCat.{r}} (a : g.rings.obj B ⟶ B')


private theorem insertion_underlying (i : Insertion g nY nX φ a) (M : Mod J B) :
    (underlying (g.rings.obj R)).map (i.ordinary.app M) =
      (g.inverse R).moduleUnderlying.hom.app ((restriction φ).obj M) ≫
        pullbackInsertion g nX a M := by
  ext U x
  change (i.ordinary.app M).val.app U x =
    ((nX.ordinaryAdjunction a).unit.app _).val.app U
      (((g.inverse R).moduleUnderlying.hom.app ((restriction φ).obj M) ≫
        (g.inverse B).moduleUnderlying.inv.app M).hom.app U x)
  rw [nX.ordinary_unit]
  exact i.sections M U x

private theorem pullback_preserves_flat [PreservesFiniteLimits uInv]
    (P : CochainComplex (Mod J B) ℤ) (hk : P.IsKFlatIndependentCoefficients)
    (hf : ∀ j : ℤ, IsFlatOnSite (J := J) (R := B) (P.X j)) :
    flatTerms (((ordinaryPullback g (pX := pX) a).mapHomologicalComplex (.up ℤ)).obj P) := by
  exact isKFlat_ringedToposPullback uInv uPush adj (g.inverse B) a
    (ordinaryPullback g (pX := pX) a)
    (fun M ↦ (pX a).obj_eq ((g.inverse B).modules.obj M))
    (fun f ↦ (pX a).map_eq ((g.inverse B).modules.map f)) P hk hf

include nX in
private theorem pullback_computation_iso [PreservesFiniteLimits uInv]
    (P : CochainComplex (Mod J B) ℤ) (hk : P.IsKFlatIndependentCoefficients)
    (hf : ∀ j : ℤ, IsFlatOnSite (J := J) (R := B) (P.X j)) :
    IsIso (pullbackComputation g (pX := pX) a ((HomotopyCategory.quotient _ _).obj P)) := by
  obtain ⟨hi, ht⟩ := inverse_preserves_flat g nX B P hk hf
  have hc := nX.computed a
    (((g.inverse B).modules.mapHomologicalComplex (.up ℤ)).obj P) hi ht
  change IsIso ((pX a).counit.app
    (((g.inverse B).modules.mapHomotopyCategory (.up ℤ)).obj
      ((HomotopyCategory.quotient _ _).obj P))) at hc
  dsimp only [pullbackComputation]
  infer_instance

private theorem target_computation_iso [PreservesFiniteLimits uInv]
    (P : CochainComplex (Mod J B) ℤ) (hk : P.IsKFlatIndependentCoefficients)
    (hf : ∀ j : ℤ, IsFlatOnSite (J := J) (R := B) (P.X j)) :
    IsIso (targetComputation g nX φ a ((HomotopyCategory.quotient _ _).obj P)) := by
  have := pullback_computation_iso g nX a P hk hf
  dsimp only [targetComputation]
  infer_instance

private theorem comp_inv_app {V W E : Type*} [Category V] [Category W]
    [Category E] [Preadditive V] [Preadditive W] [Preadditive E]
    (F : V ⥤ W) (G : W ⥤ E) [F.Additive] [G.Additive]
    (H : HomotopyCategory V (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app H = 𝟙 _ := by
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective H
  exact (HomotopyCategory.quotient _ _).map_id _

variable {Z : Type c} [Category.{v} Z] [EssentiallySmall.{r} Z]
  {L : GrothendieckTopology Z}
  {vInv : Sheaf K (Type r) ⥤ Sheaf L (Type r)}
  {vPush : Sheaf L (Type r) ⥤ Sheaf K (Type r)} {vadj : vInv ⊣ vPush}
  {wInv : Sheaf J (Type r) ⥤ Sheaf L (Type r)}
  {wPush : Sheaf L (Type r) ⥤ Sheaf J (Type r)} {wadj : wInv ⊣ wPush}
  (g2 : Geometry vInv vPush vadj) (g12 : Geometry wInv wPush wadj)
  {pZ : Scalars.{c, v, r} L} (nZ : SuccessiveDerivedQuotient.Normalization (J := L) pZ)
  {B2 : Sheaf L CommRingCat.{r}} (a2 : g2.rings.obj B' ⟶ B2)
  (a12 : g12.rings.obj B ⟶ B2)
  (θ : wInv ≅ uInv ⋙ vInv) (ρ : g12.rings ≅ g.rings ⋙ g2.rings)


private theorem ordinary_composition
    (i1 : Insertion g nY nX φ a)
    (i2 : Insertion g2 nX nZ (g.rings.map φ ≫ a) a2)
    (i12 : Insertion g12 nY nZ φ a12)
    (d : CompositionData g nY nX φ a g2 g12 nZ a2 a12 θ ρ) (M : Mod J B) :
    i12.ordinary.app M ≫ d.target.ordinary.hom.app M =
      d.source.ordinary.hom.app M ≫
        (restriction (ρ.hom.app R)).map
          ((g2.inverse (g.rings.obj R)).modules.map (i1.ordinary.app M) ≫
            i2.ordinary.app ((ordinaryPullback g (pX := pX) a).obj M)) := by
  apply (underlying (g12.rings.obj R)).map_injective
  rw [Functor.map_comp, insertion_underlying, Category.assoc, d.target_sections]
  change _ = (underlying (g12.rings.obj R)).map (d.source.ordinary.hom.app M) ≫
    (underlying (g2.rings.obj (g.rings.obj R))).map
      ((g2.inverse (g.rings.obj R)).modules.map (i1.ordinary.app M) ≫
        i2.ordinary.app ((ordinaryPullback g (pX := pX) a).obj M))
  rw [Functor.map_comp, insertion_underlying]
  have hn := (g2.inverse (g.rings.obj R)).moduleUnderlying.hom.naturality
    (i1.ordinary.app M)
  dsimp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  erw [insertion_underlying g nY nX φ a i1 M]
  rw [vInv.map_comp]
  have hs := congrArg (fun f ↦ f ≫ vInv.map (pullbackInsertion g nX a M) ≫
    pullbackInsertion g2 nZ a2 ((ordinaryPullback g (pX := pX) a).obj M))
      (d.source_sections M)
  have ht : θ.hom.app ((underlying B).obj M) =
      θ.hom.app ((underlying R).obj ((restriction φ).obj M)) := by rfl
  rw [ht]
  simpa only [Category.assoc] using hs.symm

set_option maxHeartbeats 800000 in
-- Pasting the independent derived-category factor maps requires substantial defeq reduction.
private theorem inner_square
    (i1 : Insertion g nY nX φ a)
    (i2 : Insertion g2 nX nZ (g.rings.map φ ≫ a) a2)
    (P : CochainComplex (Mod J B) ℤ) (hk : P.IsKFlatIndependentCoefficients)
    (hf : ∀ j : ℤ, IsFlatOnSite (J := J) (R := B) (P.X j))
    (hp : flatTerms
      (((ordinaryPullback g (pX := pX) a).mapHomologicalComplex (.up ℤ)).obj P)) :
    (g2.left (g.rings.obj R)).map (i1.derived.app (DerivedCategory.Q.obj P)) ≫
      i2.derived.app ((derivedPullback g (pX := pX) a).obj (DerivedCategory.Q.obj P)) ≫
      (target g2 nZ (g.rings.map φ ≫ a) a2).map
        (pullbackComputation g (pX := pX) a ((HomotopyCategory.quotient _ _).obj P)) ≫
      targetComputation g2 nZ (g.rings.map φ ≫ a) a2
        (((ordinaryPullback g (pX := pX) a).mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj P)) =
    (g2.left (g.rings.obj R)).map
      (sourceComputation g nY φ ((HomotopyCategory.quotient _ _).obj P)) ≫
      (g2.inverse (g.rings.obj R)).modules.mapDerivedCategoryFactorsh.hom.app
        (((ordinarySource g φ).mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj P)) ≫
      DerivedCategory.Qh.map
        (((g2.inverse (g.rings.obj R)).modules.mapHomotopyCategory (.up ℤ)).map
          ((NatTrans.mapHomotopyCategory i1.ordinary (.up ℤ)).app
            ((HomotopyCategory.quotient _ _).obj P)) ≫
          (NatTrans.mapHomotopyCategory i2.ordinary (.up ℤ)).app
            (((ordinaryPullback g (pX := pX) a).mapHomotopyCategory (.up ℤ)).obj
              ((HomotopyCategory.quotient _ _).obj P))) := by
  let H := (HomotopyCategory.quotient (Mod J B) (.up ℤ)).obj P
  let P1 := ((ordinaryPullback g (pX := pX) a).mapHomologicalComplex (.up ℤ)).obj P
  let H1 := (HomotopyCategory.quotient (Mod K B') (.up ℤ)).obj P1
  have h1 := i1.representative P hk hf
  have h2 := i2.representative P1 hp.1 hp.2
  have hn := i2.derived.naturality (pullbackComputation g (pX := pX) a H)
  dsimp only [Functor.comp_map] at hn
  dsimp only [targetComputation] at h1
  erw [Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    DerivedCategory.Qh.map_id, Category.comp_id] at h1
  dsimp only [sourceComputation] at h2
  erw [comp_inv_app, DerivedCategory.Qh.map_id, Category.comp_id] at h2
  have h1' := congrArg ((g2.left (g.rings.obj R)).map) h1
  simp only [Functor.map_comp] at h1'
  erw [← reassoc_of% hn]
  erw [h2]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% h1']
  have hκ := (g2.inverse (g.rings.obj R)).modules.mapDerivedCategoryFactorsh.hom.naturality
    ((NatTrans.mapHomotopyCategory i1.ordinary (.up ℤ)).app H)
  dsimp only [Functor.comp_map] at hκ
  erw [reassoc_of% hκ]
  rfl


private theorem model_comp_computation {A B E : Type*}
    [Category A] [Category B] [Category E] [Abelian A] [Abelian B] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory E]
    (F : Model A B) (G : Model B E) (H : HomotopyCategory A (.up ℤ)) :
    (F.comp G).computation H = G.derived.map (F.computation H) ≫
      G.computation ((F.ordinary.mapHomotopyCategory (.up ℤ)).obj H) := by
  dsimp only [Model.comp]
  erw [Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    DerivedCategory.Qh.map_id, Category.comp_id]

private theorem homotopy_paste {A B C D E : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D] [Preadditive E]
    (F : A ⥤ B) (P : A ⥤ D) (G : D ⥤ B) (I : B ⥤ C) (T : D ⥤ C) (R : C ⥤ E)
    [F.Additive] [P.Additive] [G.Additive] [I.Additive] [T.Additive] [R.Additive]
    (α : F ⟶ P ⋙ G) (β : G ⋙ I ⟶ T) (X : CochainComplex A ℤ) :
    (R.mapHomotopyCategory (.up ℤ)).map
      ((I.mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory α (.up ℤ)).app
          ((HomotopyCategory.quotient A (.up ℤ)).obj X)) ≫
        (NatTrans.mapHomotopyCategory β (.up ℤ)).app
          ((HomotopyCategory.quotient D (.up ℤ)).obj
            ((P.mapHomologicalComplex (.up ℤ)).obj X))) =
      (NatTrans.mapHomotopyCategory
        (Functor.whiskerRight (Functor.whiskerRight α I ≫ Functor.whiskerLeft P β) R)
        (.up ℤ)).app ((HomotopyCategory.quotient A (.up ℤ)).obj X) := by
  change (R.mapHomotopyCategory (.up ℤ)).map
    ((I.mapHomotopyCategory (.up ℤ)).map
      ((HomotopyCategory.quotient B (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex α (.up ℤ)).app X)) ≫
      (HomotopyCategory.quotient C (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex β (.up ℤ)).app
          ((P.mapHomologicalComplex (.up ℤ)).obj X))) = _
  rw [Functor.map_comp, Functor.mapHomotopyCategory_map,
    Functor.mapHomotopyCategory_map, Functor.mapHomotopyCategory_map]
  rw [← (HomotopyCategory.quotient E (.up ℤ)).map_comp]
  change (HomotopyCategory.quotient E (.up ℤ)).map _ =
    (HomotopyCategory.quotient E (.up ℤ)).map _
  congr 1
  ext j
  change R.map (I.map (α.app (X.X j))) ≫ R.map (β.app (P.obj (X.X j))) =
    R.map (I.map (α.app (X.X j)) ≫ β.app (P.obj (X.X j)))
  rw [Functor.map_comp]

set_option maxHeartbeats 800000 in
-- The normalized composite contains several independent localization universe presentations.
private theorem representative_composition [PreservesFiniteLimits uInv]
    [PreservesFiniteLimits vInv]
    (i1 : Insertion g nY nX φ a)
    (i2 : Insertion g2 nX nZ (g.rings.map φ ≫ a) a2)
    (i12 : Insertion g12 nY nZ φ a12)
    (d : CompositionData g nY nX φ a g2 g12 nZ a2 a12 θ ρ)
    (P : CochainComplex (Mod J B) ℤ) (hk : P.IsKFlatIndependentCoefficients)
    (hf : ∀ j : ℤ, IsFlatOnSite (J := J) (R := B) (P.X j)) :
    i12.derived.app (DerivedCategory.Q.obj P) ≫
      d.target.derived.hom.app (DerivedCategory.Q.obj P) =
    d.source.derived.hom.app (DerivedCategory.Q.obj P) ≫
      (nZ.right (ρ.hom.app R)).map
        ((g2.left (g.rings.obj R)).map (i1.derived.app (DerivedCategory.Q.obj P)) ≫
          i2.derived.app ((derivedPullback g (pX := pX) a).obj
            (DerivedCategory.Q.obj P))) := by
  let H := (HomotopyCategory.quotient (Mod J B) (.up ℤ)).obj P
  let P1 := ((ordinaryPullback g (pX := pX) a).mapHomologicalComplex (.up ℤ)).obj P
  have hp := pullback_preserves_flat g (pX := pX) a P hk hf
  let H1 := (HomotopyCategory.quotient (Mod K B') (.up ℤ)).obj P1
  let T := (((pullbackModel g (pX := pX) a).comp
    (targetModel g2 nZ (g.rings.map φ ≫ a) a2)).comp
      (restrictionModel nZ (ρ.hom.app R)))
  have hi : IsIso (T.computation H) := by
    have h1 := pullback_computation_iso g nX a P hk hf
    have h2 := target_computation_iso g2 nZ (g.rings.map φ ≫ a) a2 P1 hp.1 hp.2
    change IsIso (pullbackComputation g (pX := pX) a H) at h1
    change IsIso (targetComputation g2 nZ (g.rings.map φ ≫ a) a2
      (((ordinaryPullback g (pX := pX) a).mapHomotopyCategory (.up ℤ)).obj H)) at h2
    dsimp only [T, Model.comp, pullbackModel, targetModel, restrictionModel]
    infer_instance
  let S := (((sourceModel g nY φ).comp (inverseModel g2 (R := g.rings.obj R))).comp
    (restrictionModel nZ (ρ.hom.app R)))
  let βo := Functor.whiskerRight
    (Functor.whiskerRight i1.ordinary (g2.inverse (g.rings.obj R)).modules ≫
      Functor.whiskerLeft (ordinaryPullback g (pX := pX) a) i2.ordinary)
        (restriction (ρ.hom.app R))
  have hpaste : (nZ.right (ρ.hom.app R)).map
      ((g2.left (g.rings.obj R)).map (i1.derived.app (DerivedCategory.Q.obj P)) ≫
        i2.derived.app ((derivedPullback g (pX := pX) a).obj (DerivedCategory.Q.obj P))) ≫
        T.computation H = S.computation H ≫
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory βo (.up ℤ)).app H) := by
    dsimp only [S, T]
    erw [model_comp_computation, model_comp_computation,
      model_comp_computation, model_comp_computation]
    dsimp only [restrictionModel, pullbackModel, targetModel, sourceModel, inverseModel]
    erw [Category.assoc]
    change (nZ.right (ρ.hom.app R)).map
        ((g2.left (g.rings.obj R)).map (i1.derived.app (DerivedCategory.Q.obj P)) ≫
          i2.derived.app ((derivedPullback g (pX := pX) a).obj (DerivedCategory.Q.obj P))) ≫
        (nZ.right (ρ.hom.app R)).map
          ((target g2 nZ (g.rings.map φ ≫ a) a2).map
            (pullbackComputation g (pX := pX) a H) ≫
              targetComputation g2 nZ (g.rings.map φ ≫ a) a2 H1) ≫
        (nZ.right_factors (ρ.hom.app R)).hom.app
          (((ordinaryTarget g2 (pX := pZ) (g.rings.map φ ≫ a) a2).mapHomotopyCategory
            (.up ℤ)).obj H1) =
      (nZ.right (ρ.hom.app R)).map
        ((g2.left (g.rings.obj R)).map (sourceComputation g nY φ H) ≫
          (g2.inverse (g.rings.obj R)).modules.mapDerivedCategoryFactorsh.hom.app
            (((ordinarySource g φ).mapHomotopyCategory (.up ℤ)).obj H)) ≫
        (nZ.right_factors (ρ.hom.app R)).hom.app
          (((g2.inverse (g.rings.obj R)).modules.mapHomotopyCategory (.up ℤ)).obj
            (((ordinarySource g φ).mapHomotopyCategory (.up ℤ)).obj H)) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory βo (.up ℤ)).app H)
    have hi := inner_square g nY nX φ a g2 nZ a2 i1 i2 P hk hf hp
    let z := ((g2.inverse (g.rings.obj R)).modules.mapHomotopyCategory (.up ℤ)).map
      ((NatTrans.mapHomotopyCategory i1.ordinary (.up ℤ)).app H) ≫
      (NatTrans.mapHomotopyCategory i2.ordinary (.up ℤ)).app H1
    have hn := (nZ.right_factors (ρ.hom.app R)).hom.naturality z
    dsimp only [Functor.comp_map] at hn
    rw [← Category.assoc, ← Functor.map_comp]
    simp only [Category.assoc]
    erw [hi]
    have hz : ((restriction (ρ.hom.app R)).mapHomotopyCategory (.up ℤ)).map z =
        (NatTrans.mapHomotopyCategory βo (.up ℤ)).app H := by
      exact homotopy_paste (ordinarySource g φ) (ordinaryPullback g (pX := pX) a)
        (restriction (g.rings.map φ ≫ a)) (g2.inverse (g.rings.obj R)).modules
        (ordinaryTarget g2 (pX := pZ) (g.rings.map φ ≫ a) a2)
        (restriction (ρ.hom.app R)) i1.ordinary i2.ordinary P
    have hh := congrArg (fun f ↦ (nZ.right (ρ.hom.app R)).map
      ((g2.left (g.rings.obj R)).map (sourceComputation g nY φ H) ≫
        (g2.inverse (g.rings.obj R)).modules.mapDerivedCategoryFactorsh.hom.app
          (((ordinarySource g φ).mapHomotopyCategory (.up ℤ)).obj H)) ≫ f) hn
    erw [hz] at hh
    simp only [z, Functor.map_comp, Category.assoc] at hh ⊢
    convert hh using 1
    all_goals rfl
  apply (cancel_mono (T.computation H)).mp
  rw [Category.assoc, d.target.representative P ⟨hk, hf⟩]
  dsimp only [targetModel]
  rw [← Category.assoc]
  erw [i12.representative P hk hf]
  rw [Category.assoc]
  have he : i12.ordinary ≫ d.target.ordinary.hom =
      d.source.ordinary.hom ≫ βo := by
    apply NatTrans.ext
    funext M
    exact ordinary_composition g nY nX φ a g2 g12 nZ a2 a12 θ ρ i1 i2 i12 d M
  have heh := congrArg (fun f ↦ (NatTrans.mapHomotopyCategory f (.up ℤ)).app H) he
  simp only [NatTrans.mapHomotopyCategory_comp, NatTrans.comp_app] at heh
  simp only [Category.assoc]
  erw [hpaste]
  rw [← DerivedCategory.Qh.map_comp]
  erw [heh]
  rw [DerivedCategory.Qh.map_comp, ← Category.assoc]
  erw [← d.source.representative P ⟨hk, hf⟩]
  exact Category.assoc _ _ _


/-- Scalar insertion commutes with normalized pullback composition before reduction.

Source: Stacks Project, sites-cohomology.tex, Tag 0D6D; sites-modules.tex, Tag 03EL.
(blueprint: lem-weil-pbc-common-quotient-insertion-composition).

Proof: the underlying source compositor is the inverse-image compositor. Under this
identification, the first insertion sends a section to 1 tensor that section, and
the second to 1 tensor (1 tensor that section). The target compositor is normalized
on precisely these insertions, hence collapses this to the composite insertion.
Naturality of the inverse-image compositor and the module-underlying isomorphisms
makes this an equality of ordinary module morphisms. On a flat-term K-flat complex,
pullback remains K-flat with flat terms by 0G7E, so both insertion representative
squares apply. Paste them with the source and target ModelIso representative squares;
naturality of exact inverse image and restriction computation maps identifies the
pasting with the derived expression below. Cancel the invertible computation maps.
Flat-term K-flat resolutions and localization then detect equality of the two natural
transformations on every derived object. No quotient, flat coefficient restriction,
or finite-comparison existence is used in this unreduced coherence argument. -/
theorem insertion_composition [PreservesFiniteLimits uInv] [PreservesFiniteLimits vInv]
    (i1 : Insertion g nY nX φ a)
    (i2 : Insertion g2 nX nZ (g.rings.map φ ≫ a) a2)
    (i12 : Insertion g12 nY nZ φ a12)
    (d : CompositionData g nY nX φ a g2 g12 nZ a2 a12 θ ρ) (M : D J B) :
    i12.derived.app M ≫ d.target.derived.hom.app M =
      d.source.derived.hom.app M ≫
        (nZ.right (ρ.hom.app R)).map
          ((g2.left (g.rings.obj R)).map (i1.derived.app M) ≫
            i2.derived.app ((derivedPullback g (pX := pX) a).obj M)) := by
  let β := Functor.whiskerRight
    (Functor.whiskerRight i1.derived (g2.left (g.rings.obj R)) ≫
      Functor.whiskerLeft (derivedPullback g (pX := pX) a) i2.derived)
        (nZ.right (ρ.hom.app R))
  have he : i12.derived ≫ d.target.derived.hom = d.source.derived.hom ≫ β := by
    let P := flatHomotopy (J := J) B
    let L := P.ι ⋙ (DerivedCategory.Qh : HomotopyCategory (Mod J B) (.up ℤ) ⥤ D J B)
    let W := (HomotopyCategory.quasiIso (Mod J B) (.up ℤ)).inverseImage P.ι
    have : L.IsLocalization W := flat_localization (J := J) B
    apply Localization.natTrans_ext L W
    intro H
    exact representative_composition g nY nX φ a g2 g12 nZ a2 a12 θ ρ i1 i2 i12 d
      H.obj.as H.property.1 H.property.2
  exact NatTrans.congr_app he M


end SheafOfModules.CommonQuotientPullback
