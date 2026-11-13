/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import WeilConjectures.AlgebraicGeometry.DerivedOpenCrossComponentsIsIso
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful

/-! # The difference diagram for arbitrary ambient opens

## References

* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem isIso_split_matrix
    {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {P Q R S : C} (f : P ⟶ R) (a : P ⟶ S) (b : Q ⟶ S)
    [IsIso f] [IsIso b] :
    IsIso (biprod.lift (biprod.fst ≫ f) (biprod.desc a b)) := by
  let e : P ⊞ Q ≅ R ⊞ S :=
    { hom := biprod.lift (biprod.fst ≫ f) (biprod.desc a b)
      inv := biprod.desc
        (biprod.lift (inv f) (-(inv f ≫ a ≫ inv b))) (biprod.lift 0 (inv b))
      hom_inv_id := by
        ext <;> simp [Preadditive.comp_add, Preadditive.add_comp,
          Preadditive.comp_neg, Category.assoc]
      inv_hom_id := by
        ext <;> simp [Preadditive.neg_comp, Category.assoc] }
  exact e.isIso_hom

private theorem isIso_mapped_split_matrix
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] [PreservesBinaryBiproducts F] {P Q T : C} {R : D}
    (f : F.obj P ⟶ R) (a : P ⟶ T) (b : Q ⟶ T)
    [IsIso f] [IsIso (F.map b)] :
    IsIso (biprod.lift (F.map biprod.fst ≫ f) (F.map (biprod.desc a b))) := by
  have := isIso_split_matrix f (F.map a) (F.map b)
  have h : biprod.lift (F.map biprod.fst ≫ f) (F.map (biprod.desc a b)) =
      (F.mapBiprod P Q).hom ≫
        biprod.lift (biprod.fst ≫ f) (biprod.desc (F.map a) (F.map b)) := by
    ext <;> simp [biprod.desc_eq, Category.assoc]
  rw [h]
  infer_instance

private theorem isIso_mapped_split_matrix_snd
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] [PreservesBinaryBiproducts F] {P Q T : C} {R : D}
    (f : F.obj Q ⟶ R) (a : P ⟶ T) (b : Q ⟶ T)
    [IsIso f] [IsIso (F.map a)] :
    IsIso (biprod.lift (F.map biprod.snd ≫ f) (F.map (biprod.desc a b))) := by
  have := isIso_split_matrix f (F.map b) (F.map a)
  have h : biprod.lift (F.map biprod.snd ≫ f) (F.map (biprod.desc a b)) =
      ((F.mapBiprod P Q).hom ≫ (biprod.braiding _ _).hom) ≫
        biprod.lift (biprod.fst ≫ f) (biprod.desc (F.map b) (F.map a)) := by
    ext
    · simp [Category.assoc]
    · simp [Category.assoc, biprod.braiding_hom, biprod.desc_eq,
        Preadditive.comp_add, add_comm]
  rw [h]
  infer_instance

private theorem difference_compatibility
    {C CU CV CW : Type*} [Category C] [Category CU] [Category CV] [Category CW]
    [Preadditive C] [Preadditive CU] [Preadditive CV] [Preadditive CW]
    [HasBinaryBiproducts C]
    (rU : C ⥤ CU) (rV : C ⥤ CV) (sU : CU ⥤ CW) (sV : CV ⥤ CW) (rW : C ⥤ CW)
    [sU.Additive] [sV.Additive] [rW.Additive]
    (eU : rU ⋙ sU ≅ rW) (eV : rV ⋙ sV ≅ rW)
    {AU BV T : C} {A : CU} {B : CV}
    (f : rU.obj AU ⟶ A) (g : rV.obj BV ⟶ B) (c : sU.obj A ⟶ sV.obj B)
    (a : AU ⟶ T) (b : BV ⟶ T) (k : rW.obj T ⟶ sV.obj B)
    (ha : rW.map a ≫ k = eU.inv.app AU ≫ sU.map f ≫ c)
    (hb : rW.map b ≫ k = eV.inv.app BV ≫ sV.map g) :
    eU.inv.app (AU ⊞ BV) ≫ sU.map (rU.map biprod.fst ≫ f) ≫ c -
      eV.inv.app (AU ⊞ BV) ≫ sV.map (rV.map biprod.snd ≫ g) =
        rW.map (biprod.desc a (-b)) ≫ k := by
  simp only [Functor.map_comp, Category.assoc]
  rw [biprod.desc_eq]
  simp only [Functor.map_add, Functor.map_comp, Functor.map_neg,
    Preadditive.add_comp, Preadditive.neg_comp, Preadditive.comp_neg, Category.assoc]
  rw [ha, hb]
  simp only [← Functor.comp_map]
  rw [← eU.inv.naturality_assoc, ← eV.inv.naturality_assoc]
  exact sub_eq_add_neg _ _

set_option backward.isDefEq.respectTransparency false in
private theorem open_counit_isIso (X : Scheme.{u}) (O : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings O.toScheme.toRingedSpace))]
    (adj : (schemeOpenRestriction X O).mapDerivedCategory ⊣ schemeDerivedDirectImage O.ι)
    (M : schemeDerivedCategory O.toScheme) : IsIso (adj.counit.app M) := by
  let F := RingedSpace.moduleDirectImage O.ι.toLRSHom.toShHom
  let a : schemeOpenRestriction X O ⊣ F :=
    (Scheme.Modules.restrictAdjunction O.ι).ofNatIsoLeft
      (Scheme.Modules.overFunctorEquiv O).symm
  have : F.Full := inferInstanceAs (Scheme.Modules.pushforward O.ι).Full
  have : F.Faithful := inferInstanceAs (Scheme.Modules.pushforward O.ι).Faithful
  have : F.PreservesKInjectiveComplexes := a.preservesKInjectiveComplexes
  have : (schemeDerivedDirectImage O.ι).Full :=
    inferInstanceAs F.rightDerivedFunctor.Full
  have : (schemeDerivedDirectImage O.ι).Faithful :=
    inferInstanceAs F.rightDerivedFunctor.Faithful
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 400000 in
-- The threefold transported restriction needs additional instance search.
set_option maxHeartbeats 600000 in
-- The derived restriction functors and their comparisons need this elaboration budget.
/-- The difference arrow has split normal form on each of the two opens.
The middle and last objects are the explicit direct-image sum and overlap image.
This constructs their maps, not a glued object. -/
theorem relative_open_difference_diagram
    (X : Scheme.{u}) (U V : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))]
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (c : (schemeOpenOverlapRestriction X
        (homOfLE inf_le_left : U ⊓ V ⟶ U)).mapDerivedCategory.obj A ≅
      (schemeOpenOverlapRestriction X
        (homOfLE inf_le_right : U ⊓ V ⟶ V)).mapDerivedCategory.obj B) :
    let rU := (schemeOpenRestriction X U).mapDerivedCategory;
    let rV := (schemeOpenRestriction X V).mapDerivedCategory;
    let sU := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_left : U ⊓ V ⟶ U)).mapDerivedCategory;
    let sV := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_right : U ⊓ V ⟶ V)).mapDerivedCategory;
    let rW := (schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory;
    let eU := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_left : U ⊓ V ⟶ U);
    let eV := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_right : U ⊓ V ⟶ V);
    let E := (schemeDerivedDirectImage U.ι).obj A ⊞ (schemeDerivedDirectImage V.ι).obj B;
    let D := (schemeDerivedDirectImage (U ⊓ V).ι).obj (sV.obj B);
    ∃ (d : E ⟶ D)
      (pU : rU.obj E ⟶ A) (pV : rV.obj E ⟶ B)
      (k : rW.obj D ⟶ sV.obj B),
      IsIso (biprod.lift pU (rU.map d)) ∧
      IsIso (biprod.lift pV (rV.map d)) ∧
      eU.inv.app E ≫ sU.map pU ≫ c.hom - eV.inv.app E ≫ sV.map pV = rW.map d ≫ k := by
  classical
  let adj (O : X.Opens)
      [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings O.toScheme.toRingedSpace))] :
      (schemeOpenRestriction X O).mapDerivedCategory ⊣ schemeDerivedDirectImage O.ι :=
    by
      let a : schemeOpenRestriction X O ⊣
          RingedSpace.moduleDirectImage O.ι.toLRSHom.toShHom :=
        (Scheme.Modules.restrictAdjunction O.ι).ofNatIsoLeft
          (Scheme.Modules.overFunctorEquiv O).symm
      exact a.mapDerivedCategoryRightDerivedAdjunction
  let adjU := adj U
  let adjV := adj V
  let adjW := adj (U ⊓ V)
  dsimp only
  let rU := (schemeOpenRestriction X U).mapDerivedCategory
  let rV := (schemeOpenRestriction X V).mapDerivedCategory
  let sU := (schemeOpenOverlapRestriction X
    (homOfLE inf_le_left : U ⊓ V ⟶ U)).mapDerivedCategory
  let sV := (schemeOpenOverlapRestriction X
    (homOfLE inf_le_right : U ⊓ V ⟶ V)).mapDerivedCategory
  let rW := (schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory
  have : rU.Additive := inferInstanceAs (schemeOpenRestriction X U).mapDerivedCategory.Additive
  have : rV.Additive := inferInstanceAs (schemeOpenRestriction X V).mapDerivedCategory.Additive
  let eU := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_left : U ⊓ V ⟶ U)
  let eV := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_right : U ⊓ V ⟶ V)
  let AU := (schemeDerivedDirectImage U.ι).obj A
  let BV := (schemeDerivedDirectImage V.ι).obj B
  let a : AU ⟶ (schemeDerivedDirectImage (U ⊓ V).ι).obj (sV.obj B) :=
    adjW.homEquiv _ _ (eU.inv.app AU ≫ sU.map (adjU.counit.app A) ≫ c.hom)
  let b : BV ⟶ (schemeDerivedDirectImage (U ⊓ V).ι).obj (sV.obj B) :=
    adjW.homEquiv _ _ (eV.inv.app BV ≫ sV.map (adjV.counit.app B))
  obtain ⟨hU, hV⟩ := derived_open_cross_components_isIso X U V A B c adjU adjV adjW
  refine ⟨biprod.desc a (-b),
    rU.map biprod.fst ≫ adjU.counit.app A,
    rV.map biprod.snd ≫ adjV.counit.app B, adjW.counit.app (sV.obj B), ?_, ?_, ?_⟩
  · have : IsIso (rU.map b) := hU
    have : IsIso (rU.map (-b)) := by
      rw [Functor.map_neg]
      exact (-asIso (rU.map b)).isIso_hom
    have : IsIso (adjU.counit.app A) := open_counit_isIso X U adjU A
    have : rU.IsLeftAdjoint := adjU.isLeftAdjoint
    have : PreservesBinaryBiproducts rU :=
      preservesBinaryBiproducts_of_preservesBinaryProducts rU
    exact isIso_mapped_split_matrix rU (adjU.counit.app A) a (-b)
  · have : IsIso (rV.map a) := hV
    have : IsIso (adjV.counit.app B) := open_counit_isIso X V adjV B
    have : rV.IsLeftAdjoint := adjV.isLeftAdjoint
    have : PreservesBinaryBiproducts rV :=
      preservesBinaryBiproducts_of_preservesBinaryProducts rV
    exact isIso_mapped_split_matrix_snd rV (adjV.counit.app B) a (-b)
  · have ha : rW.map a ≫ adjW.counit.app (sV.obj B) =
        eU.inv.app AU ≫ sU.map (adjU.counit.app A) ≫ c.hom := by
      exact (adjW.homEquiv _ _).symm_apply_apply _
    have hb : rW.map b ≫ adjW.counit.app (sV.obj B) =
        eV.inv.app BV ≫ sV.map (adjV.counit.app B) := by
      exact (adjW.homEquiv _ _).symm_apply_apply _
    exact difference_compatibility rU rV sU sV rW eU eV
      (adjU.counit.app A) (adjV.counit.app B) c.hom a b
      (adjW.counit.app (sV.obj B)) ha hb

end AlgebraicGeometry
