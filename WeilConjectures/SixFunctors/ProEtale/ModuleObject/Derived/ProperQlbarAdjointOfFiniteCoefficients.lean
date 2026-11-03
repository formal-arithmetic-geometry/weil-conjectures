/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import
  WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import
  WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedQbarScalarBasisSections
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedQbarScalarBasisUnitOfSections
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientRestrictionConstructible
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import all WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CondensedCompactSupportProjectionCore
import all WeilConjectures.SmoothPurity.FilteredCondensedRepresentingPair.FilteredCondensedCounitFiniteFormula
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

/-! # Descent of proper adjunctions from finite coefficient fields

Source: current blueprint, proper algebraic-closure coefficient adjoint proof,
steps 1--4 (blueprint: lem-sfb-proper-qlbar-adjoint-of-finite-coefficients).
This is the coefficient-descent step, separated from integral proper-adjoint existence.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Mod.extendScalars
  CategoryTheory.Mod.derivedExtendMapDerivedCategoryAdjunction
  HasDerivedCategory.standard HasDerivedCategory.ofHasKInjectiveResolutions
  _root_.instCategoryDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  AlgebraicGeometry Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj CategoryTheory.Functor


universe w v u' v' ux vx uy vy

-- Universal-counit descent, adapted from CondensedQbarExceptionalAdjointColimit.
-- Faithful additive scalar extensions replace its normalization and Hom-injectivity step.
private structure ProperDescentData
    {I : Type w} [Preorder I]
    {CX : I → Type u} [∀ i, Category.{v} (CX i)]
    {CY : I → Type u'} [∀ i, Category.{v'} (CY i)]
    {DX : Type ux} [Category.{vx} DX] {DY : Type uy} [Category.{vy} DY]
    (cX : CategoryCocone (C := CX) (D := DX))
    (cY : CategoryCocone (C := CY) (D := DY)) where
  F : ∀ i, CX i ⥤ CY i
  G : ∀ i, CY i ⥤ CX i
  adjunction : ∀ i, F i ⊣ G i
  b : ∀ {i j : I} (h : i ≤ j), F i ⋙ cY.T h ≅ cX.T h ⋙ F j
  c : ∀ {i j : I} (h : i ≤ j), G i ⋙ cX.T h ≅ cY.T h ⋙ G j
  counit_compatibility : ∀ {i j : I} (h : i ≤ j) (y : CY i),
    (cY.T h).map ((adjunction i).counit.app y) =
      (b h).hom.app ((G i).obj y) ≫
        (F j).map ((c h).hom.app y) ≫
        (adjunction j).counit.app ((cY.T h).obj y)

namespace ProperDescentProof

variable {I : Type w} [Preorder I]
  {CX : I → Type u} [∀ i, Category.{v} (CX i)]
  {CY : I → Type u'} [∀ i, Category.{v'} (CY i)]
  {DX : Type ux} [Category.{vx} DX] {DY : Type uy} [Category.{vy} DY]
  {cX : CategoryCocone (C := CX) (D := DX)}
  {cY : CategoryCocone (C := CY) (D := DY)}
  (data : ProperDescentData cX cY) (FΩ : DX ⥤ DY)
  (α : ∀ i, cX.Φ i ⋙ FΩ ≅ data.F i ⋙ cY.Φ i)
  (alpha_compatibility : ∀ {i j : I} (h : i ≤ j) (x : CX i),
    FΩ.map ((cX.iso h).hom.app x) ≫ (α i).hom.app x =
      (α j).hom.app ((cX.T h).obj x) ≫
        (cY.Φ j).map ((data.b h).inv.app x) ≫
          (cY.iso h).hom.app ((data.F i).obj x))

private def counitAt (i : I) (y : CY i) :
    FΩ.obj ((cX.Φ i).obj ((data.G i).obj y)) ⟶ (cY.Φ i).obj y :=
  (α i).hom.app ((data.G i).obj y) ≫ (cY.Φ i).map ((data.adjunction i).counit.app y)

private noncomputable def valueTransition {i j : I} (h : i ≤ j) (y : CY i) :
    (cX.Φ i).obj ((data.G i).obj y) ≅
      (cX.Φ j).obj ((data.G j).obj ((cY.T h).obj y)) :=
  ((cX.iso h).app ((data.G i).obj y)).symm ≪≫
    (cX.Φ j).mapIso ((data.c h).app y)

include alpha_compatibility in
private theorem alpha_inv_transition {i j : I} (h : i ≤ j) (x : CX i) :
    FΩ.map ((cX.iso h).inv.app x) ≫ (α j).hom.app ((cX.T h).obj x) =
      (α i).hom.app x ≫ (cY.iso h).inv.app ((data.F i).obj x) ≫
        (cY.Φ j).map ((data.b h).hom.app x) := by
  apply (cancel_epi (FΩ.map ((cX.iso h).hom.app x))).mp
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rw [← Category.assoc, alpha_compatibility h x]
  simp

include alpha_compatibility in
private theorem counitAt_transition {i j : I} (h : i ≤ j) (y : CY i) :
    FΩ.map (valueTransition data h y).hom ≫
        counitAt data FΩ α j ((cY.T h).obj y) ≫ (cY.iso h).hom.app y =
      counitAt data FΩ α i y := by
  have hn := (α j).hom.naturality ((data.c h).hom.app y)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  dsimp only [valueTransition, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    Functor.mapIso_hom, Iso.app_hom, counitAt]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn,
    reassoc_of% (alpha_inv_transition data FΩ α alpha_compatibility h
      ((data.G i).obj y))]
  simp only [← Functor.map_comp_assoc]
  rw [← data.counit_compatibility h y]
  simpa only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Category.assoc] using
    congrArg ((α i).hom.app ((data.G i).obj y) ≫ ·)
      (NatIso.naturality_1 (cY.iso h) ((data.adjunction i).counit.app y))

private def representativeX {i j k : I} (hi : i ≤ k) (hj : j ≤ k)
    (x : CX i) (y : CX j) (g : (cX.T hi).obj x ⟶ (cX.T hj).obj y) :
    (cX.Φ i).obj x ⟶ (cX.Φ j).obj y :=
  (cX.iso hi).inv.app x ≫ (cX.Φ k).map g ≫ (cX.iso hj).hom.app y

include alpha_compatibility in
private theorem counitAt_formula {i j k : I} (hi : i ≤ k) (hj : j ≤ k)
    (x : CX i) (y : CY j)
    (g : (cX.T hi).obj x ⟶ (cX.T hj).obj ((data.G j).obj y)) :
    FΩ.map (representativeX hi hj x ((data.G j).obj y) g) ≫ counitAt data FΩ α j y =
      (α i).hom.app x ≫ (cY.iso hi).inv.app ((data.F i).obj x) ≫
        (cY.Φ k).map ((data.b hi).hom.app x ≫
          ((data.adjunction k).homEquiv _ _).symm (g ≫ (data.c hj).hom.app y)) ≫
        (cY.iso hj).hom.app y := by
  let g' := g ≫ (data.c hj).hom.app y
  have ht := counitAt_transition data FΩ α alpha_compatibility hj y
  have hcan : FΩ.map (representativeX hi hj x ((data.G j).obj y) g) ≫
        counitAt data FΩ α j y =
      FΩ.map ((cX.iso hi).inv.app x) ≫ FΩ.map ((cX.Φ k).map g') ≫
        counitAt data FΩ α k ((cY.T hj).obj y) ≫ (cY.iso hj).hom.app y := by
    rw [← ht]
    simp [representativeX, valueTransition, g', Functor.map_comp]
  rw [hcan]
  dsimp only [counitAt]
  have hn := (α k).hom.naturality g'
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [Category.assoc]
  rw [reassoc_of% hn,
    reassoc_of% (alpha_inv_transition data FΩ α alpha_compatibility hi x)]
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc, g']


variable [∀ i, Preadditive (CX i)] [∀ i, Preadditive (CY i)]
  [Preadditive DX] [Preadditive DY]
  [∀ i, (cX.Φ i).Additive] [∀ i, (cY.Φ i).Additive]
  [∀ i, (data.F i).Additive] [FΩ.Additive]
  [∀ i, (cY.Φ i).Faithful]

include alpha_compatibility in
private theorem counitAt_bijective_models
    (hX : cX.HomSurj) (hY : cY.HomSurj)
    (i j : I) (x : CX i) (y : CY j) :
    Function.Bijective (fun g : (cX.Φ i).obj x ⟶ (cX.Φ j).obj ((data.G j).obj y) ↦
      FΩ.map g ≫ counitAt data FΩ α j y) := by
  have kernel (f : (cX.Φ i).obj x ⟶ (cX.Φ j).obj ((data.G j).obj y))
      (hf : FΩ.map f ≫ counitAt data FΩ α j y = 0) : f = 0 := by
    obtain ⟨k, hi, hj, f', he⟩ := hX i j x ((data.G j).obj y) f
    rw [he] at hf
    change FΩ.map (representativeX hi hj x ((data.G j).obj y) f') ≫
      counitAt data FΩ α j y = 0 at hf
    rw [counitAt_formula data FΩ α alpha_compatibility] at hf
    have hz : (cY.Φ k).map ((data.b hi).hom.app x ≫
        ((data.adjunction k).homEquiv _ _).symm (f' ≫ (data.c hj).hom.app y)) = 0 := by
      exact zero_of_comp_mono ((cY.iso hj).hom.app y)
        (zero_of_epi_comp ((cY.iso hi).inv.app ((data.F i).obj x))
          (zero_of_epi_comp ((α i).hom.app x) hf))
    have hz' := (cY.Φ k).map_injective (hz.trans ((cY.Φ k).map_zero _ _).symm)
    have hz'' : ((data.adjunction k).homEquiv _ _).symm
        (f' ≫ (data.c hj).hom.app y) = 0 := by
      exact zero_of_epi_comp ((data.b hi).hom.app x) hz'
    have hf' : f' ≫ (data.c hj).hom.app y = 0 := by
      apply ((data.adjunction k).homEquiv _ _).symm.injective
      simpa only [Adjunction.homEquiv_counit, Functor.map_zero, zero_comp] using hz''
    have hf'' : f' = 0 := zero_of_comp_mono ((data.c hj).hom.app y) hf'
    rw [he, hf'']
    simp only [Functor.map_zero, zero_comp, comp_zero]
  constructor
  · intro f g he
    apply sub_eq_zero.mp
    apply kernel
    simp only [Functor.map_sub, Preadditive.sub_comp, he, sub_self]
  · intro f
    obtain ⟨k, hi, hj, g, hg⟩ := hY i j ((data.F i).obj x) y
      ((α i).inv.app x ≫ f)
    let t := (data.adjunction k).homEquiv _ _ ((data.b hi).inv.app x ≫ g)
    refine ⟨representativeX hi hj x ((data.G j).obj y)
      (t ≫ (data.c hj).inv.app y), ?_⟩
    dsimp only
    rw [counitAt_formula data FΩ α alpha_compatibility]
    dsimp only [t]
    simp only [Functor.comp_obj, Category.assoc, Iso.inv_hom_id_app, Category.comp_id,
      Equiv.symm_apply_apply, Functor.map_comp]
    have hc : (cY.Φ k).map ((data.b hi).hom.app x) ≫
        (cY.Φ k).map ((data.b hi).inv.app x) = 𝟙 _ := by
      rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
    rw [reassoc_of% hc, ← hg]
    simp

include alpha_compatibility in
private theorem counitAt_bijective
    (hX : cX.IsFilteredTwoColimit) (hY : cY.HomSurj)
    (j : I) (y : CY j) (K : DX) :
    Function.Bijective (fun g : K ⟶ (cX.Φ j).obj ((data.G j).obj y) ↦
      FΩ.map g ≫ counitAt data FΩ α j y) := by
  obtain ⟨i, x, ⟨s⟩⟩ := hX.essSurjObj K
  have hb := counitAt_bijective_models data FΩ α alpha_compatibility hX.homSurj hY i j x y
  constructor
  · intro f g he
    apply (cancel_epi s.hom).mp
    apply hb.1
    simpa only [Functor.map_comp, Category.assoc] using congrArg (FΩ.map s.hom ≫ ·) he
  · intro f
    obtain ⟨g, hg⟩ := hb.2 (FΩ.map s.hom ≫ f)
    refine ⟨s.inv ≫ g, ?_⟩
    simp only [Functor.map_comp, Category.assoc, hg, Iso.map_inv_hom_id_assoc]

include alpha_compatibility in
private theorem isLeftAdjoint
    (hX : cX.IsFilteredTwoColimit) (hY : cY.IsFilteredTwoColimit) :
    FΩ.IsLeftAdjoint := by
  classical
  let eps := counitAt data FΩ α
  have hb := counitAt_bijective data FΩ α alpha_compatibility hX hY.homSurj
  choose idx mdl hs using hY.essSurjObj
  let s (y : DY) := (hs y).some
  let obj (y : DY) := (cX.Φ (idx y)).obj ((data.G (idx y)).obj (mdl y))
  let counit (y : DY) : FΩ.obj (obj y) ⟶ y := eps (idx y) (mdl y) ≫ (s y).hom
  have bij (K : DX) (y : DY) :
      Function.Bijective (fun g : K ⟶ obj y ↦ FΩ.map g ≫ counit y) := by
    constructor
    · intro f g h
      apply (hb (idx y) (mdl y) K).1
      apply (cancel_mono (s y).hom).mp
      simpa only [counit, Category.assoc] using h
    · intro f
      obtain ⟨g, hg⟩ := (hb (idx y) (mdl y) K).2 (f ≫ (s y).inv)
      change FΩ.map g ≫ eps (idx y) (mdl y) = f ≫ (s y).inv at hg
      refine ⟨g, ?_⟩
      dsimp only [counit]
      rw [← Category.assoc, hg]
      simp
  let e (K : DX) (y : DY) : (FΩ.obj K ⟶ y) ≃ (K ⟶ obj y) :=
    (Equiv.ofBijective _ (bij K y)).symm
  have es (K : DX) (y : DY) (f : FΩ.obj K ⟶ y) :
      FΩ.map (e K y f) ≫ counit y = f := (e K y).symm_apply_apply f
  have en (K' K : DX) (y : DY) (f : K' ⟶ K) (g : FΩ.obj K ⟶ y) :
      e K' y (FΩ.map f ≫ g) = f ≫ e K y g := by
    apply (bij K' y).1
    dsimp only
    rw [Functor.map_comp, Category.assoc, es, es]
  exact (Adjunction.adjunctionOfEquivRight e en).isLeftAdjoint

end ProperDescentProof

private instance toClosureAdditive (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    (constructibleToPadicAlgCl X ℓ E).Additive := by
  have hi :=
    (Mod.extendScalars
      (padicSubfieldRingObjToPadicAlgCl X ℓ E)).leftDerivedFunctorIsoMapDerivedCategory
  have : (derivedExtendScalarsToPadicAlgCl X ℓ E).Additive :=
    Functor.additive_of_iso hi.symm
  unfold constructibleToPadicAlgCl
  infer_instance

private instance toClosureFaithful (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    (constructibleToPadicAlgCl X ℓ E).Faithful := by
  have : (derivedExtendScalarsToPadicAlgCl X ℓ E).Faithful :=
    faithful_leftDerivedExtendScalarsToPadicAlgCl X ℓ E
  unfold constructibleToPadicAlgCl
  infer_instance

namespace ProperFiniteCoefficientProof

variable (ℓ : ℕ) [Fact ℓ.Prime]
  (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
  {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)

private theorem restriction_mem (K : PadicSubfieldConstructible X ℓ F) :
    boundedConstructible (padicSubfieldRingObj X ℓ E)
      ((Mod.comap (padicSubfieldRingObjMap X ℓ h)).mapDerivedCategory.obj K.obj) := by
  let R := Mod.comap (D := Sheaf (ProEt.topology X) Ab.{u + 1})
    (padicSubfieldRingObjMap X ℓ h)
  refine ⟨R.bounded_mapDerivedCategory_obj K.property.1, fun q ↦ ?_⟩
  exact IsConstructibleModuleObject.of_iso
    ((R.mapDerivedCategoryHomologyFunctorIso q).app K.obj)
    (finiteCoefficientRestriction_constructible X ℓ h _ (K.property.2 q))

private noncomputable def restriction :
    PadicSubfieldConstructible X ℓ F ⥤ PadicSubfieldConstructible X ℓ E :=
  (boundedConstructible (padicSubfieldRingObj X ℓ E)).lift
    ((boundedConstructible (padicSubfieldRingObj X ℓ F)).ι ⋙
      (Mod.comap (padicSubfieldRingObjMap X ℓ h)).mapDerivedCategory)
    (restriction_mem ℓ X h)

private noncomputable def scalarAdjunction :
    constructibleExtendScalars X ℓ h ⊣ restriction ℓ X h :=
  (Mod.derivedExtendMapDerivedCategoryAdjunction
      (padicSubfieldRingObjMap X ℓ h)).restrictFullyFaithful (ObjectProperty.fullyFaithfulι _)
      (ObjectProperty.fullyFaithfulι _) (Iso.refl _) (Iso.refl _)

private theorem scalarAdjunction_unit (K : PadicSubfieldConstructible X ℓ E) :
    ((scalarAdjunction ℓ X h).unit.app K).hom =
      (Mod.derivedExtendMapDerivedCategoryAdjunction
        (padicSubfieldRingObjMap X ℓ h)).unit.app K.obj := by
  change (boundedConstructible (padicSubfieldRingObj X ℓ E)).ι.map
    ((scalarAdjunction ℓ X h).unit.app K) = _
  simp only [scalarAdjunction, Adjunction.map_restrictFullyFaithful_unit_app,
    Iso.refl_hom, NatTrans.id_app]
  dsimp only [constructibleExtendScalars, restriction, ObjectProperty.lift_obj_obj,
    Functor.comp_obj, ObjectProperty.ι_obj]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id]

private instance restrictionReflects : (restriction ℓ X h).ReflectsIsomorphisms := by
  have : (Mod.comap (D := Sheaf (ProEt.topology X) Ab.{u + 1})
      (padicSubfieldRingObjMap X ℓ h)).ReflectsIsomorphisms :=
    Mod.restrictionReflectsIsomorphisms _
  have : (Mod.comap (D := Sheaf (ProEt.topology X) Ab.{u + 1})
      (padicSubfieldRingObjMap X ℓ h)).mapDerivedCategory.ReflectsIsomorphisms :=
    CondensedRing.reflectsDerivedIsomorphisms _
  refine ⟨fun f hf ↦ ?_⟩
  have : IsIso ((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι.map
      ((restriction ℓ X h).map f)) := inferInstance
  change IsIso ((Mod.comap (padicSubfieldRingObjMap X ℓ h)).mapDerivedCategory.map f.hom)
    at this
  have hi : IsIso f.hom := isIso_of_reflects_iso _
    (Mod.comap (padicSubfieldRingObjMap X ℓ h)).mapDerivedCategory
  have : IsIso ((boundedConstructible (padicSubfieldRingObj X ℓ F)).ι.map f) := hi
  exact isIso_of_reflects_iso f (boundedConstructible _).ι


private noncomputable def center (τ : CatCenter
    (DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (padicSubfieldRingObj X ℓ E)))) :
    CatCenter (PadicSubfieldConstructible X ℓ E) where
  app K := ⟨τ.app K.obj⟩
  naturality K L f := by
    apply ObjectProperty.hom_ext
    exact τ.naturality f.hom


set_option maxHeartbeats 1000000 in
-- Scalar-change diagrams involve several derived and restriction functors.
set_option synthInstance.maxHeartbeats 100000 in
-- The diagrams involve categories of internal modules and their full subcategories.
private theorem unit_copower
    (I : Type (u + 1)) [Finite I]
    (b : I → (𝟙_ (Sheaf (ProEt.topology X) Ab.{u + 1}) ⟶ padicSubfieldRingObj X ℓ F))
    (hu : ∀ (N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (padicSubfieldRingObj X ℓ E)) [HasCoproduct (fun _ : I ↦ N)],
      IsIso (Sigma.desc (f := fun _ : I ↦ N) fun i ↦
        (Mod.extendRestrictAdjunction (padicSubfieldRingObjMap X ℓ h)).unit.app N ≫
          (Mod.comap (padicSubfieldRingObjMap X ℓ h)).map
            (Mod.qbar_scalarEndo (b i)
              ((Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).obj N))))
    (K : PadicSubfieldConstructible X ℓ E) :
    IsIso (Sigma.desc (f := fun _ : I ↦ K) fun i ↦
      (scalarAdjunction ℓ X h).unit.app K ≫ (restriction ℓ X h).map
        ((center ℓ X (E := F) (qbar_derivedCenter (Mod.qbar_scalarNatEndo (b i)))).app
          ((constructibleExtendScalars X ℓ h).obj K))) := by
  let ι := (boundedConstructible (padicSubfieldRingObj X ℓ E)).ι
  let d := Sigma.desc (f := fun _ : I ↦ K) fun i ↦
    (scalarAdjunction ℓ X h).unit.app K ≫ (restriction ℓ X h).map
      ((center ℓ X (E := F) (qbar_derivedCenter (Mod.qbar_scalarNatEndo (b i)))).app
        ((constructibleExtendScalars X ℓ h).obj K))
  change IsIso d
  have hunit := qbar_isIso_unit (padicSubfieldRingObjMap X ℓ h) b (fun N ↦ hu N) K.obj
  have he : sigmaComparison ι (fun _ : I ↦ K) ≫ ι.map d =
      Sigma.desc (f := fun _ : I ↦ K.obj) fun i ↦
        Mod.qbar_scalarUnitLeg (padicSubfieldRingObjMap X ℓ h) (b i) K.obj := by
    dsimp only [d]
    rw [sigmaComparison_map_desc]
    apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_desc]
    change ((scalarAdjunction ℓ X h).unit.app K).hom ≫
      (Mod.comap (padicSubfieldRingObjMap X ℓ h)).mapDerivedCategory.map
        ((qbar_derivedCenter (Mod.qbar_scalarNatEndo (b i))).app
          ((constructibleExtendScalars X ℓ h).obj K).obj) = _
    rw [scalarAdjunction_unit, Mod.qbar_scalarUnitLeg_eq]
    rfl
  have : IsIso (sigmaComparison ι (fun _ : I ↦ K) ≫ ι.map d) := by
    rw [he]
    exact hunit
  have : IsIso (ι.map d) :=
    IsIso.of_isIso_comp_left (sigmaComparison ι (fun _ : I ↦ K)) _
  exact isIso_of_reflects_iso d ι

end ProperFiniteCoefficientProof

namespace ProperScalarProof

open WeilConjectures.CompactSupportCondensedRealization

set_option maxHeartbeats 1000000 in
-- Scalar-change diagrams involve several derived and restriction functors.
set_option synthInstance.maxHeartbeats 100000 in
-- The diagrams involve categories of internal modules and their full subcategories.
private theorem push_comp_tensor
    {Λ Λ' Λ'' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    [MonObj Λ''] [IsCommMonObj Λ'']
    (a : Λ ⟶ Λ') [IsMonHom a] [FlatCoefficientMap a]
    (b : Λ' ⟶ Λ'') [IsMonHom b] [FlatCoefficientMap b]
    (e : Λ ⟶ Λ'') [IsMonHom e] [FlatCoefficientMap e] (he : a ≫ b = e)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (condensedScalar b Y).map ((CondensedRing.derivedPushHom a f).app K) ≫
      (CondensedRing.derivedPushHom b f).app ((condensedScalar a X).obj K) ≫
      (CondensedRing.lowerStar Λ'' f).rightDerivedFunctor.map
        (((Functor.leftDerivedFunctorCompIso
            (Mod.extendScalars (coefficientMap a X))
            (Mod.extendScalars (coefficientMap b X))).symm ≪≫
          Functor.leftDerivedFunctorNatIso _
            ((Mod.extendScalarsComp _ _).symm ≪≫
              Mod.extendScalarsIsoOfEq
                ((coefficientMap_comp a b X).symm.trans
                  (congrArg (fun α ↦ coefficientMap α X) he)))).hom.app K) =
      ((Functor.leftDerivedFunctorCompIso
          (Mod.extendScalars (coefficientMap a Y))
          (Mod.extendScalars (coefficientMap b Y))).symm ≪≫
        Functor.leftDerivedFunctorNatIso _
          ((Mod.extendScalarsComp _ _).symm ≪≫
            Mod.extendScalarsIsoOfEq
              ((coefficientMap_comp a b Y).symm.trans
                (congrArg (fun α ↦ coefficientMap α Y) he)))).hom.app
          ((CondensedRing.lowerStar Λ f).rightDerivedFunctor.obj K) ≫
        (CondensedRing.derivedPushHom e f).app K := by
  subst e
  have hc := scalarPush_comp a b f K
  simp only [WeilConjectures.FilteredCondensedRepresentingPair.scalar_tensor] at hc
  dsimp only [condensedPushScalar, condensedScalarAdjunction,
    CondensedRing.derivedPushHom] at hc ⊢
  exact hc

attribute [local irreducible] CondensedRing.derivedPushHom

variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (p : Z ⟶ Y) [IsProper p.left]

private noncomputable def finiteIso
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    CondensedRing.ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E p ⋙
        constructibleExtendScalars Y.left ℓ h ≅
      constructibleExtendScalars Z.left ℓ h ⋙
        CondensedRing.ContinuousMapRingObj.boundedConstructibleLowerStar ℓ F p :=
  NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _
      ((asIso (CondensedRing.derivedPushHom
        (Profinite.padicSubfieldRingObjMap ℓ h) p.left)).app K.obj))
    (by
      intro K L f
      apply ObjectProperty.hom_ext
      exact (CondensedRing.derivedPushHom
        (Profinite.padicSubfieldRingObjMap ℓ h) p.left).naturality f.hom)

private noncomputable def omegaIso (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    CondensedRing.ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E p ⋙
        constructibleToPadicAlgCl Y.left ℓ E ≅
      constructibleToPadicAlgCl Z.left ℓ E ⋙ CondensedRing.boundedConstructibleLowerStar ℓ p :=
  NatIso.ofComponents
    (fun K ↦ by
      have hi := CondensedRing.isIso_derivedPushHom_padicAlgCl_of_boundedBelow_of_isProper
        ℓ E p.left ⟨K.obj, K.property.1.1⟩
      exact ObjectProperty.isoMk _
        (asIso ((CondensedRing.derivedPushHom
          (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) p.left).app K.obj)))
    (by
      intro K L f
      apply ObjectProperty.hom_ext
      exact (CondensedRing.derivedPushHom
        (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) p.left).naturality f.hom)

set_option maxHeartbeats 1000000 in
-- Scalar-change diagrams involve several derived and restriction functors.
set_option synthInstance.maxHeartbeats 100000 in
-- The diagrams involve categories of internal modules and their full subcategories.
private theorem field_cocycle {E F : PadicAlgCl.FiniteIntermediateField ℓ}
    (h : E ≤ F) (K : PadicSubfieldConstructible Z.left ℓ E) :
    (constructibleToPadicAlgCl Y.left ℓ F).map ((finiteIso ℓ p h).hom.app K) ≫
      (omegaIso ℓ p F).hom.app ((constructibleExtendScalars Z.left ℓ h).obj K) ≫
      (CondensedRing.boundedConstructibleLowerStar ℓ p).map
        ((constructibleToPadicAlgClCompIso Z.left ℓ h).hom.app K) =
      (constructibleToPadicAlgClCompIso Y.left ℓ h).hom.app
        ((CondensedRing.ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E p).obj K) ≫
        (omegaIso ℓ p E).hom.app K := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, toAlgCl_map_hom,
    CondensedRing.boundedConstructibleLowerStar, ObjectProperty.lift_map,
    ObjectProperty.homMk, Functor.comp_map, ObjectProperty.ι_map,
    tensorComp_hom, ← tensorComp_eq]
  simpa only [finiteIso, omegaIso, ObjectProperty.isoMk_hom,
    ObjectProperty.homMk, NatIso.ofComponents_hom_app, Iso.app_hom, asIso_hom,
    condensedScalar, derivedExtendScalarsCompIso, derivedExtendScalarsToPadicAlgCl,
    derivedExtendScalarsSubfield, constructibleExtendScalars, constructibleToPadicAlgCl,
    CondensedRing.ContinuousMapRingObj.boundedConstructibleLowerStar,
    ObjectProperty.lift_obj_obj, ObjectProperty.ι_obj, Functor.comp_obj,
    padicSubfieldRingObjMap, padicSubfieldRingObjToPadicAlgCl] using
    (push_comp_tensor (Profinite.padicSubfieldRingObjMap ℓ h)
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F)
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
      (Profinite.padicSubfieldRingObjMap_comp_toPadicAlgCl ℓ h) p.left K.obj)


attribute [local irreducible] finiteIso omegaIso
  ProperFiniteCoefficientProof.scalarAdjunction ProperFiniteCoefficientProof.restriction

omit [IsProper p.left] in
set_option maxHeartbeats 1000000 in
-- Scalar-change diagrams involve several derived and restriction functors.
set_option synthInstance.maxHeartbeats 100000 in
-- The diagrams involve categories of internal modules and their full subcategories.
end ProperScalarProof

attribute [local irreducible] AlgebraicGeometry.ProEtale.CondensedRing.derivedPushHom

@[expose] public section

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option maxHeartbeats 1000000 in
-- Assembling the adjunctions checks several derived coefficient functors.
set_option synthInstance.maxHeartbeats 100000 in
-- Scalar additivity and faithfulness are inferred through constructible inclusions.
/-- If proper pushforward has right adjoints for all finite coefficient extensions, those
adjunctions descend to algebraic-closure coefficients. The base field need not be finite
or algebraically closed; no absolute cohomological-dimension bound is used in this step.

Source: current blueprint `lem-sfb-dc-proper-pushforward-left-adjoint-qlbar` proof, steps 1--4;
Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Theorem 7.7 and Lemma 7.9;
Bhatt--Scholze, The pro-etale topology for schemes, Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-sfb-proper-qlbar-adjoint-of-finite-coefficients)

Proof:
1. For each finite extension choose the right adjoint of the actual restricted proper
pushforward supplied by `hE`. Right adjoints are determined up to the unique
counit-compatible isomorphism, so these choices require no arbitrary geometric data.
2. Restriction between finite coefficient fields preserves bounded constructibility and
is right adjoint to the actual scalar extension. A finite coefficient basis gives invertible
coproducts of scalar-unit legs. The finite proper pushforward comparison has an invertible
iterated mate, and pushforward commutes with the basis scalar actions. Its right adjoint
therefore does too. Since right adjoints here are additive, they preserve the finite
coproducts; conservative restriction and the unit-copower criterion make the finite
right-adjoint comparisons invertible. Their defining mate equation compares the counits.
3. Object and Hom descent hold for the actual filtered coefficient cocones. The proper
algebraic-closure pushforward comparison is invertible on bounded-below objects. Composition
of coefficient-push comparisons, expressed using the derived tensor associators, proves
the cocycle equation for this comparison on the bounded constructible subcategories.
4. For each finite model, extend its finite counit using the proper comparison. These
candidate universal counits are compatible with extension to a larger coefficient field.
Hom-surjectivity moves an arbitrary arrow to a common finite field, where the finite
adjunction supplies its transpose. A map in the kernel similarly descends, and faithfulness
of extension to the algebraic closure plus the finite Hom equivalence makes it zero.
Additivity proves injectivity by subtraction. Object descent extends the bijections to
all objects. These universal counits give natural Hom equivalences, hence a right adjoint
of the actual algebraic-closure pushforward.
This proves only the coefficient-descent step; integral existence is an independent input.
-/
theorem properPushforwardLeftAdjointQlbar_of_finiteCoefficients
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {Z Y : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (p : Z ⟶ Y) [IsProper p.left]
    (hE : ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      (ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E p).IsLeftAdjoint) :
    (boundedConstructibleLowerStar ℓ p).IsLeftAdjoint := by
  classical
  let : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  let : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  let : IsNoetherian Z.left := {}
  let : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  let : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  let : IsNoetherian Y.left := {}
  let P (E : PadicAlgCl.FiniteIntermediateField ℓ) :=
    ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E p
  have : ∀ E, (P E).IsLeftAdjoint := hE
  let G (E : PadicAlgCl.FiniteIntermediateField ℓ) := (P E).rightAdjoint
  let adj (E : PadicAlgCl.FiniteIntermediateField ℓ) : P E ⊣ G E :=
    Adjunction.ofIsLeftAdjoint (P E)
  let b {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :=
    ProperScalarProof.finiteIso ℓ p h
  have hi {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
      IsIso (mateEquiv (adj E) (adj F) (b h).inv) :=
    ProperScalarProof.finite_mate_isIso ℓ p G adj h
  let c {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
      G E ⋙ constructibleExtendScalars Z.left ℓ h ≅
        constructibleExtendScalars Y.left ℓ h ⋙ G F := by
    have := hi h
    exact asIso (mateEquiv (adj E) (adj F) (b h).inv)
  have hc {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
      (K : PadicSubfieldConstructible Y.left ℓ E) :
      (constructibleExtendScalars Y.left ℓ h).map ((adj E).counit.app K) =
        (b h).hom.app ((G E).obj K) ≫ (P F).map ((c h).hom.app K) ≫
          (adj F).counit.app ((constructibleExtendScalars Y.left ℓ h).obj K) := by
    have hm := mateEquiv_counit (adj E) (adj F) (b h).inv K
    simpa only [c, asIso_hom, Category.assoc, Iso.hom_inv_id_app_assoc] using
      (congrArg ((b h).hom.app ((G E).obj K) ≫ ·) hm).symm
  let data : ProperDescentData (constructibleCocone Z.left ℓ) (constructibleCocone Y.left ℓ) :=
    { F := P
      G := G
      adjunction := adj
      b := b
      c := c
      counit_compatibility := hc }
  let α (E : PadicAlgCl.FiniteIntermediateField ℓ) := (ProperScalarProof.omegaIso ℓ p E).symm
  have hα {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
      (K : PadicSubfieldConstructible Z.left ℓ E) :
      (boundedConstructibleLowerStar ℓ p).map
          ((constructibleToPadicAlgClCompIso Z.left ℓ h).hom.app K) ≫ (α E).hom.app K =
        (α F).hom.app ((constructibleExtendScalars Z.left ℓ h).obj K) ≫
          (constructibleToPadicAlgCl Y.left ℓ F).map ((b h).inv.app K) ≫
            (constructibleToPadicAlgClCompIso Y.left ℓ h).hom.app ((P E).obj K) := by
    dsimp only [α, Iso.symm_hom]
    apply (Iso.eq_inv_comp ((ProperScalarProof.omegaIso ℓ p F).app
      ((constructibleExtendScalars Z.left ℓ h).obj K))).2
    apply (Iso.eq_inv_comp
      ((constructibleToPadicAlgCl Y.left ℓ F).mapIso ((b h).app K))).2
    simp only [← Category.assoc]
    apply (Iso.comp_inv_eq ((ProperScalarProof.omegaIso ℓ p E).app K)).2
    simpa only [Category.assoc, Functor.mapIso_hom, Iso.app_hom, Functor.comp_obj, b, P]
      using ProperScalarProof.field_cocycle ℓ p h K
  have : ∀ E, ((constructibleCocone Z.left ℓ).Φ E).Additive := by
    intro E
    change (constructibleToPadicAlgCl Z.left ℓ E).Additive
    infer_instance
  have : ∀ E, ((constructibleCocone Y.left ℓ).Φ E).Additive := by
    intro E
    change (constructibleToPadicAlgCl Y.left ℓ E).Additive
    infer_instance
  have : ∀ E, ((constructibleCocone Y.left ℓ).Φ E).Faithful := by
    intro E
    change (constructibleToPadicAlgCl Y.left ℓ E).Faithful
    infer_instance
  exact ProperDescentProof.isLeftAdjoint data (boundedConstructibleLowerStar ℓ p) α hα
    (constructibleCocone_isFilteredTwoColimit Z.left ℓ)
    (constructibleCocone_isFilteredTwoColimit Y.left ℓ)

#print axioms properPushforwardLeftAdjointQlbar_of_finiteCoefficients

end AlgebraicGeometry.ProEtale.CondensedRing
