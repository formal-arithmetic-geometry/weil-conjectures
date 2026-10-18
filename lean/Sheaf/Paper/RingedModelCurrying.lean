/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.Paper.RingedLocalizationModels
public import Sheaf.Algebra.Homology.KFlatRHomCurrying
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle

/-! # Currying with an arbitrary K-flat coefficient sheaf

Source: Stacks Project, Tags 08J9 and 0A90.
(blueprint: lem-weil-pbc-ringed-model-currying).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
namespace CategoryTheory.LocalizationRHom

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})

/-- A sheaf coefficient regarded as a degree-zero derived object.
Source: Stacks 08J9 (blueprint: lem-weil-pbc-ringed-model-currying). -/
abbrev derivedCoefficient (U : C) (S : localizationModules (R.over U)) :=
  (localizationQ (R.over U)).obj
    ((HomologicalComplex.single (localizationModules (R.over U)) (.up ℤ) 0).obj S)

/-- Restrict a complex and tensor its terms by the specified sheaf coefficient.
Source: Stacks 08J9 and 0A90 (blueprint: lem-weil-pbc-ringed-model-currying). -/
abbrev coefficientComplex (U : C) (S : localizationModules (R.over U)) :=
  localizationComplexRestriction R U ⋙ localizationTensorComplex (R.over U) S

/-- Complexes whose restriction to the specified slice is K-flat.
Source: Stacks 0A96 (blueprint: lem-weil-pbc-ringed-model-currying). -/
abbrev modelObjects (U : C) : ObjectProperty (CochainComplex (localizationModules R) ℤ) :=
  fun P ↦ KFlatRHom.flat (R.over U) ((localizationComplexRestriction R U).obj P)

/-- The restricted complex, together with its supplied K-flat certificate.
Source: Stacks 0A96 (blueprint: lem-weil-pbc-ringed-model-currying). -/
abbrev modelRestrictedFlat (U : C) :
    (modelObjects R U).FullSubcategory ⥤ (KFlatRHom.flat (R.over U)).FullSubcategory :=
  ObjectProperty.lift (KFlatRHom.flat (R.over U))
    ((modelObjects R U).ι ⋙ localizationComplexRestriction R U)
    (fun P ↦ P.property)

/-- The coefficient complex with its proved K-flatness.
Source: Stacks 06YQ (blueprint: lem-weil-pbc-ringed-model-currying). -/
abbrev modelCoefficientFlat (U : C) (S₀ : localizationModules (R.over U))
    (hS : KFlatRHom.flat (R.over U)
      ((HomologicalComplex.single (localizationModules (R.over U)) (.up ℤ) 0).obj S₀)) :
    (KFlatRHom.flat (R.over U)).FullSubcategory :=
  ⟨(HomologicalComplex.single (localizationModules (R.over U)) (.up ℤ) 0).obj
    S₀, hS⟩

/-- The arguments of the normalized K-flat currying comparison.
Source: Stacks 08J9 (blueprint: lem-weil-pbc-ringed-model-currying). -/
def modelInputs (U : C) (S₀ : localizationModules (R.over U))
    (hS : KFlatRHom.flat (R.over U)
      ((HomologicalComplex.single (localizationModules (R.over U)) (.up ℤ) 0).obj S₀)) :
    (modelObjects R U).FullSubcategoryᵒᵖ × localizationDerived R ⥤
      (KFlatRHom.flat (R.over U)).FullSubcategoryᵒᵖ ×
        ((KFlatRHom.flat (R.over U)).FullSubcategoryᵒᵖ × localizationDerived (R.over U)) :=
  let E := (modelObjects R U).FullSubcategoryᵒᵖ × localizationDerived R
  let a := (Functor.const E).obj (op (modelCoefficientFlat R U S₀ hS))
  let b := CategoryTheory.Prod.fst (modelObjects R U).FullSubcategoryᵒᵖ
    (localizationDerived R) ⋙ (modelRestrictedFlat R U).op
  let c := CategoryTheory.Prod.snd (modelObjects R U).FullSubcategoryᵒᵖ
    (localizationDerived R) ⋙ localizationDerivedRestriction R U
  a.prod' (b.prod' c)

/-- The iterated Hom in the desired currying assertion, as a functor.
Source: Stacks 08J9 (blueprint: lem-weil-pbc-ringed-model-currying). -/
def modelSource (U : C) (S₀ : localizationModules (R.over U)) :
    (modelObjects R U).FullSubcategoryᵒᵖ × localizationDerived R ⥤ localizationDerived (R.over U) :=
  let E := (modelObjects R U).FullSubcategoryᵒᵖ × localizationDerived R
  let a := CategoryTheory.Prod.fst (modelObjects R U).FullSubcategoryᵒᵖ
    (localizationDerived R) ⋙ (modelObjects R U).ι.op ⋙ (localizationQ R).op ⋙
      (localizationDerivedRestriction R U).op
  let b := CategoryTheory.Prod.snd (modelObjects R U).FullSubcategoryᵒᵖ
    (localizationDerived R) ⋙ localizationDerivedRestriction R U
  let s := (Functor.const E).obj (op (derivedCoefficient R U S₀))
  s.prod' (a.prod' b ⋙ localizationRHom (R.over U)) ⋙ localizationRHom (R.over U)

/-- Hom from the ordinary localized complex, as a functor.
Source: Stacks 08J9 (blueprint: lem-weil-pbc-ringed-model-currying). -/
def modelTarget (U : C) (S₀ : localizationModules (R.over U)) :
    (modelObjects R U).FullSubcategoryᵒᵖ × localizationDerived R ⥤ localizationDerived (R.over U) :=
  let a := CategoryTheory.Prod.fst (modelObjects R U).FullSubcategoryᵒᵖ
    (localizationDerived R) ⋙ (modelObjects R U).ι.op ⋙ (coefficientComplex R U S₀).op ⋙
      (localizationQ (R.over U)).op
  let b := CategoryTheory.Prod.snd (modelObjects R U).FullSubcategoryᵒᵖ
    (localizationDerived R) ⋙ localizationDerivedRestriction R U
  a.prod' b ⋙ localizationRHom (R.over U)

set_option maxHeartbeats 400000 in
-- Combining the two representative comparisons involves large derived-category instances.
set_option backward.isDefEq.respectTransparency false in
/-- The natural currying comparison, normalized by evaluation on Hom complexes.
The two transports are the exact restriction factorization and the degree-zero
single-tensor comparison. Thus the construction does not select an arbitrary iso.
Source: Stacks 08J9 and 0A90
(blueprint: lem-weil-pbc-ringed-model-currying). -/
@[irreducible] def modelCurryNatIso (U : C) (S₀ : localizationModules (R.over U))
    (hS : KFlatRHom.flat (R.over U)
      ((HomologicalComplex.single (localizationModules (R.over U)) (.up ℤ) 0).obj S₀)) :
    modelSource R U S₀ ≅ modelTarget R U S₀ := by
  letI := HasDerivedCategory.standard (localizationModules R)
  letI := HasDerivedCategory.standard (localizationModules (R.over U))
  letI := HasDerivedCategory.standard (SheafOfModules.{u}
    (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).over U))
  let := SheafOfModules.monoidalCategory (R.over U)
  let E := (modelObjects R U).FullSubcategoryᵒᵖ × localizationDerived R
  let p := CategoryTheory.Prod.fst (modelObjects R U).FullSubcategoryᵒᵖ (localizationDerived R)
  let b := CategoryTheory.Prod.snd (modelObjects R U).FullSubcategoryᵒᵖ
    (localizationDerived R) ⋙ localizationDerivedRestriction R U
  let s := (Functor.const E).obj (op (derivedCoefficient R U S₀))
  let H := localizationRHom (R.over U)
  let V := SheafOfModules.overFunctor.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U
  let φ := Functor.isoWhiskerLeft p
    (NatIso.op (Functor.isoWhiskerLeft (modelObjects R U).ι V.mapDerivedCategoryFactors)).symm
  let inner := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (Functor.diag E) (NatIso.prod φ (Iso.refl b))) H
  let pre := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (Functor.diag E) (NatIso.prod (Iso.refl s) inner)) H
  let S := (HomologicalComplex.single (localizationModules (R.over U)) (.up ℤ) 0).obj
    S₀
  let τ := CochainComplex.map₂HomologicalComplexObjSingleIso
    (curriedTensor (localizationModules (R.over U))) S₀
  let ψ := Functor.isoWhiskerLeft p
    (NatIso.op (Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft ((modelObjects R U).ι ⋙ localizationComplexRestriction R U) τ)
      (localizationQ (R.over U))))
  let post := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (Functor.diag E) (NatIso.prod ψ.symm (Iso.refl b))) H
  let mid := Functor.isoWhiskerLeft (modelInputs R U S₀ hS) (KFlatRHom.curryIso (R.over U))
  change modelSource R U S₀ ≅ modelTarget R U S₀
  let q := p ⋙ ((modelObjects R U).ι ⋙ localizationComplexRestriction R U ⋙
    localizationQ (R.over U)).op
  let A := s.prod' (q.prod' b ⋙ H) ⋙ H
  let t := p ⋙ ((modelObjects R U).ι ⋙ localizationComplexRestriction R U ⋙
    ((curriedTensor (localizationModules (R.over U))).map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ)).obj S ⋙ localizationQ (R.over U)).op
  let B := t.prod' b ⋙ H
  have preA : modelSource R U S₀ ≅ A := pre
  have Bpost : B ≅ modelTarget R U S₀ := post
  have a : A ≅ modelInputs R U S₀ hS ⋙ KFlatRHom.left (R.over U) := by
    refine NatIso.ofComponents (fun X ↦ Iso.refl _) ?_
    intro X Y g
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    simp only [localizationRHom, localizationQ, localizationComplexRestriction,
      derivedCoefficient, localizationModules, p, b, s, H,
      localizationDerivedRestriction, Functor.comp, Functor.prod', A, q, modelInputs,
      KFlatRHom.left,
      modelCoefficientFlat, CategoryTheory.Prod.fst_map, CategoryTheory.Prod.snd_map,
      CategoryTheory.Prod.fst_obj, CategoryTheory.Prod.snd_obj, Functor.const_obj_obj,
      ObjectProperty.ι_obj, ObjectProperty.lift, ObjectProperty.FullSubcategory.id_hom,
      Functor.const_obj_map, Functor.op_map, Functor.op_obj, unop_op, Quiver.Hom.unop_op,
      ObjectProperty.ι_map, ObjectProperty.homMk, Functor.map_id, CategoryTheory.Prod.mkHom, op_id,
      unop_id]
  have z : modelInputs R U S₀ hS ⋙ KFlatRHom.right (R.over U) ≅ B := by
    refine NatIso.ofComponents (fun X ↦ Iso.refl _) ?_
    intro X Y g
    have hi : (show modelCoefficientFlat R U S₀ hS ⟶ modelCoefficientFlat R U S₀ hS from
        unop (𝟙 (op (modelCoefficientFlat R U S₀ hS)))).hom = 𝟙 _ := rfl
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    simp only [S, hi, localizationRHom, localizationQ, localizationComplexRestriction,
      localizationModules, p, b, H, localizationDerivedRestriction, Functor.comp, Functor.prod', B,
      t, modelInputs, KFlatRHom.right, modelCoefficientFlat, KFlatRHom.total,
      CategoryTheory.Prod.fst_map,
      CategoryTheory.Prod.snd_map, CategoryTheory.Prod.fst_obj, CategoryTheory.Prod.snd_obj,
      Functor.const_obj_obj, ObjectProperty.ι_obj, ObjectProperty.lift, Functor.const_obj_map,
      Functor.op_map, Functor.op_obj, op_unop, unop_op, ObjectProperty.ι_map, ObjectProperty.homMk,
      Functor.map_id, Functor.uncurry_obj_map, NatTrans.id_app, Category.id_comp,
      CategoryTheory.Prod.mkHom, prodOpEquiv, Quiver.Hom.unop, Quiver.Hom.op]
  exact preA ≪≫ a ≪≫ mid ≪≫ z ≪≫ Bpost

set_option backward.isDefEq.respectTransparency true in
/-- The evaluation-normalized currying map for any K-flat coefficient sheaf and any
complex whose restriction is K-flat. The target can be unbounded.
The construction uses exact restriction, K-flat currying and the single-tensor iso.
Source: Stacks 08J9 and 0A90 (blueprint: lem-weil-pbc-ringed-model-currying). -/
@[irreducible] def modelCurryIso (U : C) (S : localizationModules (R.over U))
    (hS : KFlatRHom.flat (R.over U)
      ((HomologicalComplex.single (localizationModules (R.over U)) (.up ℤ) 0).obj S))
    (P : CochainComplex (localizationModules R) ℤ)
    (hP : KFlatRHom.flat (R.over U) ((localizationComplexRestriction R U).obj P))
    (N : localizationDerived R) :
    (localizationRHom (R.over U)).obj
      (op (derivedCoefficient R U S), (localizationRHom (R.over U)).obj
        (op ((localizationDerivedRestriction R U).obj ((localizationQ R).obj P)),
          (localizationDerivedRestriction R U).obj N)) ≅
    (localizationRHom (R.over U)).obj
      (op ((localizationQ (R.over U)).obj ((coefficientComplex R U S).obj P)),
        (localizationDerivedRestriction R U).obj N) :=
  (modelCurryNatIso R U S hS).app (op ⟨P, hP⟩, N)

set_option maxHeartbeats 400000 in
-- Naturality expands the paired functor maps, but not their derived-Hom bodies.
set_option backward.isDefEq.respectTransparency true in
/-- Simultaneous naturality in a chain map of localization complexes and an arbitrary
derived target morphism. No boundedness of the target is assumed.
Source: Stacks 08J9 (blueprint: lem-weil-pbc-ringed-model-currying).
Proof: Apply naturality of curryNatIso to the pair consisting of the opposite
of the given chain map and the given derived target morphism. -/
theorem modelCurryIso_natural (U : C) (S : localizationModules (R.over U))
    (hS : KFlatRHom.flat (R.over U)
      ((HomologicalComplex.single (localizationModules (R.over U)) (.up ℤ) 0).obj S))
    (P P' : CochainComplex (localizationModules R) ℤ)
    (hP : modelObjects R U P) (hP' : modelObjects R U P')
    (a : P' ⟶ P) (N N' : localizationDerived R) (b : N ⟶ N') :
    (modelCurryIso R U S hS P hP N).hom ≫ (localizationRHom (R.over U)).map
      (((localizationQ (R.over U)).map ((coefficientComplex R U S).map a)).op,
        (localizationDerivedRestriction R U).map b) =
    (localizationRHom (R.over U)).map
      (𝟙 (op (derivedCoefficient R U S)),
        (localizationRHom (R.over U)).map
          (((localizationDerivedRestriction R U).map ((localizationQ R).map a)).op,
            (localizationDerivedRestriction R U).map b)) ≫
      (modelCurryIso R U S hS P' hP' N').hom := by
  unfold modelCurryIso
  change (modelCurryNatIso R U S hS).hom.app (op ⟨P, hP⟩, N) ≫ _ =
    _ ≫ (modelCurryNatIso R U S hS).hom.app (op ⟨P', hP'⟩, N')
  simpa only [modelSource, modelTarget, Functor.comp_map, CategoryTheory.Prod.fst_map,
        CategoryTheory.Prod.snd_map,
        CategoryTheory.Prod.fst_obj, CategoryTheory.Prod.snd_obj,
        Functor.const_obj_obj, ObjectProperty.ι_obj, ObjectProperty.lift,
        ObjectProperty.FullSubcategory.id_hom,
        Functor.prod'_obj, Functor.comp_obj, Functor.prod'_map,
    Functor.const_obj_map, Functor.op_map, Functor.op_obj, op_unop, unop_op, Quiver.Hom.op_unop,
        Quiver.Hom.unop_op, ObjectProperty.ι_map, ObjectProperty.homMk,
    CategoryTheory.Prod.mkHom, Iso.app_hom] using
  ((modelCurryNatIso R U S hS).hom.naturality
    (show (op (⟨P, hP⟩ : (modelObjects R U).FullSubcategory), N) ⟶
      (op (⟨P', hP'⟩ : (modelObjects R U).FullSubcategory), N') from
      ((ObjectProperty.homMk a).op, b))).symm

end CategoryTheory.LocalizationRHom
