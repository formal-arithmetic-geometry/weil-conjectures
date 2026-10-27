/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Products.Associator
public import Sheaf.Paper.RingedTopoiCanonicalTensorComparisonOfUniverses
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Sheaf.Algebra.Homology.DerivedTensorAdditiveConstraints

/-!
# Signed calculus of shifted derived tensor morphisms

Source: literature/stacks-project/sites-cohomology.tex, Tags 0FPL and 0FPM
(blueprint: lem-pur-shifted-tensor-morphism-calculus).
-/

@[expose] public section
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
-- Keep the tensor and localization APIs folded during elaboration.
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
universe u v w

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits MonoidalCategory

universe u₁ v₁ u₂ v₂ w₁ w₂

private theorem descendTensorSwap
    {A : Type u₁} [Category.{v₁} A] {D : Type u₂} [Category.{v₂} D]
    (q : A ⥤ D) (P : ObjectProperty A) (t : A × A ⥤ A) (T : D × D ⥤ D)
    (r : (P.ι.prod P.ι) ⋙ t ⋙ q ≅ ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ T)
    (c : t ≅ CategoryTheory.Prod.swap _ _ ⋙ t)
    (hex : ∀ (U V : D × D ⥤ D)
      (e : ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ U ≅
        ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ V),
      ∃ s : U ≅ V, ∀ E F : P.FullSubcategory,
        s.app (q.obj E.obj, q.obj F.obj) = e.app (E, F))
    (hext : ∀ {U V : D × D ⥤ D} (s s' : U ≅ V),
      (∀ E F : P.FullSubcategory, s.app (q.obj E.obj, q.obj F.obj) =
        s'.app (q.obj E.obj, q.obj F.obj)) → s = s') :
    ∃! σ : T ≅ CategoryTheory.Prod.swap _ _ ⋙ T,
      ∀ (X Y : A) (hx : P X) (hy : P Y),
        r.hom.app (⟨X, hx⟩, ⟨Y, hy⟩) ≫ σ.hom.app (q.obj X, q.obj Y) =
          q.map (c.hom.app (X, Y)) ≫ r.hom.app (⟨Y, hy⟩, ⟨X, hx⟩) := by
  let e : ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ T ≅
      ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ (CategoryTheory.Prod.swap _ _ ⋙ T) :=
    r.symm ≪≫
    isoWhiskerRight (isoWhiskerLeft (P.ι.prod P.ι) c) q ≪≫
    isoWhiskerLeft (CategoryTheory.Prod.swap P.FullSubcategory P.FullSubcategory) r
  obtain ⟨σ, hσ⟩ := hex _ _ e
  have hs (X Y : A) (hx : P X) (hy : P Y) :
      r.hom.app (⟨X, hx⟩, ⟨Y, hy⟩) ≫ σ.hom.app (q.obj X, q.obj Y) =
        q.map (c.hom.app (X, Y)) ≫ r.hom.app (⟨Y, hy⟩, ⟨X, hx⟩) := by
    have ha := congrArg Iso.hom (hσ ⟨X, hx⟩ ⟨Y, hy⟩)
    change σ.hom.app (q.obj X, q.obj Y) = _ at ha
    rw [ha]
    simp only [Iso.app_hom, e, Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom,
      isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app, NatTrans.comp_app,
      Iso.hom_inv_id_app_assoc]
    rfl
  refine ⟨σ, hs, ?_⟩
  intro σ' hσ'
  apply hext
  rintro ⟨X, hx⟩ ⟨Y, hy⟩
  apply Iso.ext
  exact (cancel_epi (r.hom.app (⟨X, hx⟩, ⟨Y, hy⟩))).1
    ((hσ' X Y hx hy).trans (hs X Y hx hy).symm)

set_option backward.isDefEq.respectTransparency true in
private theorem totalSwapNaturality
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A] [BraidedCategory A]
    [∀ E F : CochainComplex A ℤ,
      CochainComplex.HasMapBifunctor E F (curriedTensor A)]
    (χ : ∀ E F : CochainComplex A ℤ,
      CochainComplex.mapBifunctor E F (curriedTensor A) ≅
        CochainComplex.mapBifunctor F E (curriedTensor A))
    (hχ : ∀ (E F : CochainComplex A ℤ) (p q : ℤ),
      CochainComplex.ιMapBifunctor E F (curriedTensor A) p q (p + q) rfl ≫
          (χ E F).hom.f (p + q) =
        ((-1 : ℤ) ^ (p * q).natAbs) • ((β_ (E.X p) (F.X q)).hom ≫
          CochainComplex.ιMapBifunctor F E (curriedTensor A) q p (p + q) (add_comm q p)))
    {E E' F F' : CochainComplex A ℤ} (f : E ⟶ E') (g : F ⟶ F') :
    HomologicalComplex.mapBifunctorMap f g (curriedTensor A) (.up ℤ) ≫ (χ E' F').hom =
      (χ E F).hom ≫ HomologicalComplex.mapBifunctorMap g f (curriedTensor A) (.up ℤ) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  subst n
  simp only [HomologicalComplex.comp_f,
    HomologicalComplex.ι_mapBifunctorMap_assoc]
  erw [hχ E' F' p q]
  conv_rhs => erw [← Category.assoc, hχ E F p q]
  simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.assoc]
  erw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [curriedTensor]
  rw [← tensorHom_def_assoc, BraidedCategory.braiding_naturality_assoc]
  rw [tensorHom_def, Category.assoc]

@[irreducible]
private def totalSwapNatIso
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A] [BraidedCategory A]
    [∀ E F : CochainComplex A ℤ,
      CochainComplex.HasMapBifunctor E F (curriedTensor A)]
    (χ : ∀ E F : CochainComplex A ℤ,
      CochainComplex.mapBifunctor E F (curriedTensor A) ≅
        CochainComplex.mapBifunctor F E (curriedTensor A))
    (hχ : ∀ (E F : CochainComplex A ℤ) (p q : ℤ),
      CochainComplex.ιMapBifunctor E F (curriedTensor A) p q (p + q) rfl ≫
          (χ E F).hom.f (p + q) =
        ((-1 : ℤ) ^ (p * q).natAbs) • ((β_ (E.X p) (F.X q)).hom ≫
          CochainComplex.ιMapBifunctor F E (curriedTensor A) q p (p + q) (add_comm q p))) :
    Functor.uncurry.obj ((curriedTensor A).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)) ≅
      CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj
        ((curriedTensor A).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)) := by
  let t := Functor.uncurry.obj
    ((curriedTensor A).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))
  have hm {E E' F F' : CochainComplex A ℤ} (f : E ⟶ E') (g : F ⟶ F') :
      t.map (Prod.mkHom f g) =
        HomologicalComplex.mapBifunctorMap f g (curriedTensor A) (.up ℤ) := by
    simp [t, Functor.map₂HomologicalComplex, Functor.uncurry_obj_map,
      HomologicalComplex.mapBifunctorMap, ← HomologicalComplex₂.total.map_comp]
  refine NatIso.ofComponents (F := t) (G := CategoryTheory.Prod.swap _ _ ⋙ t)
    (fun X ↦ χ X.1 X.2) ?_
  intro X Y f
  change t.map (X := (X.1, X.2)) (Y := (Y.1, Y.2)) (Prod.mkHom f.1 f.2) ≫
      (χ Y.1 Y.2).hom =
    (χ X.1 X.2).hom ≫
      t.map (X := (X.2, X.1)) (Y := (Y.2, Y.1)) (Prod.mkHom f.2 f.1)
  rw [hm f.1 f.2, hm f.2 f.1]
  exact totalSwapNaturality χ hχ f.1 f.2

private theorem totalSwapNatIso_hom_app
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A] [BraidedCategory A]
    [∀ E F : CochainComplex A ℤ,
      CochainComplex.HasMapBifunctor E F (curriedTensor A)]
    (χ : ∀ E F : CochainComplex A ℤ,
      CochainComplex.mapBifunctor E F (curriedTensor A) ≅
        CochainComplex.mapBifunctor F E (curriedTensor A))
    (hχ : ∀ (E F : CochainComplex A ℤ) (p q : ℤ),
      CochainComplex.ιMapBifunctor E F (curriedTensor A) p q (p + q) rfl ≫
          (χ E F).hom.f (p + q) =
        ((-1 : ℤ) ^ (p * q).natAbs) • ((β_ (E.X p) (F.X q)).hom ≫
          CochainComplex.ιMapBifunctor F E (curriedTensor A) q p (p + q) (add_comm q p)))
    (E F : CochainComplex A ℤ) :
    (totalSwapNatIso χ hχ).hom.app (E, F) = (χ E F).hom := by
  unfold totalSwapNatIso
  rfl

@[irreducible]
private def totalComplexSwap
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A] [BraidedCategory A]
    [∀ E F : CochainComplex A ℤ,
      CochainComplex.HasMapBifunctor E F (curriedTensor A)]
    (E F : CochainComplex A ℤ) :
    CochainComplex.mapBifunctor E F (curriedTensor A) ≅
      CochainComplex.mapBifunctor F E (curriedTensor A) :=
  HomologicalComplex₂.total.mapIso (CochainComplex.Monoidal.braidingBicomplexIso E F)
    (.up ℤ) ≪≫ HomologicalComplex.mapBifunctorFlipIso F E (curriedTensor A) (.up ℤ)

private theorem totalComplexSwap_signed
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A] [BraidedCategory A]
    [∀ E F : CochainComplex A ℤ,
      CochainComplex.HasMapBifunctor E F (curriedTensor A)]
    (E F : CochainComplex A ℤ) (p q : ℤ) :
    CochainComplex.ιMapBifunctor E F (curriedTensor A) p q (p + q) rfl ≫
        (totalComplexSwap E F).hom.f (p + q) =
      ((-1 : ℤ) ^ (p * q).natAbs) • ((β_ (E.X p) (F.X q)).hom ≫
        CochainComplex.ιMapBifunctor F E (curriedTensor A) q p (p + q) (add_comm q p)) := by
  have h₁ : CochainComplex.ιMapBifunctor E F (curriedTensor A) p q (p + q) rfl ≫
      (HomologicalComplex₂.total.map
        (CochainComplex.Monoidal.braidingBicomplexIso E F).hom (.up ℤ)).f (p + q) =
      (β_ (E.X p) (F.X q)).hom ≫
        CochainComplex.ιMapBifunctor E F (curriedTensor A).flip p q (p + q) rfl := by
    erw [HomologicalComplex₂.ιTotal_map]
    rfl
  simp only [totalComplexSwap, Iso.trans_hom, HomologicalComplex.comp_f,
    HomologicalComplex₂.total.mapIso_hom]
  erw [← Category.assoc, h₁]
  erw [Category.assoc, HomologicalComplex.ι_mapBifunctorFlipIso_hom, Units.smul_def,
    Preadditive.comp_zsmul]
  change ((q * p).negOnePow : ℤ) • _ = _
  rw [mul_comm q p]
  have hsign : ((p * q).negOnePow : ℤ) = (-1 : ℤ) ^ (p * q).natAbs :=
    Int.coe_negOnePow ℤ (p * q)
  erw [hsign]

private theorem exactDerivedComparison
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (E : CochainComplex A ℤ) :
    derivedPullbackComplexComparison F F.mapDerivedCategory F.mapDerivedCategoryFactorsh.hom E =
      F.mapDerivedCategoryFactors.hom.app E := by
  simp only [derivedPullbackComplexComparison,
    Functor.mapDerivedCategoryFactorsh_hom_app, Category.assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, Iso.inv_hom_id_app]
  exact Category.comp_id _

section BinaryNormalization
variable {A : Type u₁} [Category.{v₁} A] [HasShift A ℤ]
  {D : Type u₂} [Category.{v₂} D] [HasShift D ℤ]
  (q : A ⥤ D) [q.CommShift ℤ] (P : ObjectProperty A)
  (t : A × A ⥤ A) (T : D × D ⥤ D)
  (r : (P.ι.prod P.ι) ⋙ t ⋙ q ≅ ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ T)

/-- The normalization square for the two-variable shift.
Source: Stacks 0FPT (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def TensorShiftNormalization (a b : ℤ)
    (c : ((shiftFunctor A a).prod (shiftFunctor A b)) ⋙ t ≅
      t ⋙ shiftFunctor A (a + b))
    (s : ((shiftFunctor D a).prod (shiftFunctor D b)) ⋙ T ≅
      T ⋙ shiftFunctor D (a + b)) : Prop :=
  ∀ (E F : A) (hE : P E) (hF : P F),
    ∃ (hEa : P (E⟦a⟧)) (hFb : P (F⟦b⟧)),
      r.hom.app (⟨E⟦a⟧, hEa⟩, ⟨F⟦b⟧, hFb⟩) ≫
        T.map (Prod.mkHom ((q.commShiftIso a).hom.app E)
          ((q.commShiftIso b).hom.app F)) ≫ s.hom.app (q.obj E, q.obj F) =
      q.map (c.hom.app (E, F)) ≫ (q.commShiftIso (a + b)).hom.app _ ≫
        (shiftFunctor D (a + b)).map (r.hom.app (⟨E, hE⟩, ⟨F, hF⟩))

end BinaryNormalization

set_option backward.isDefEq.respectTransparency false
section GenericShiftDescent
variable {A : Type u₁} [Category.{v₁} A] [HasShift A ℤ]
  {D : Type u₂} [Category.{v₂} D] [HasShift D ℤ]
  (q : A ⥤ D) [q.CommShift ℤ] (P : ObjectProperty A)
  (t : A × A ⥤ A) (T : D × D ⥤ D)
  (r : (P.ι.prod P.ι) ⋙ t ⋙ q ≅ ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ T)
  (hshift : ∀ (E : P.FullSubcategory) (n : ℤ), P (E.obj⟦n⟧))
  (hex : ∀ (U V : D × D ⥤ D)
    (e : ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ U ≅
      ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ V),
    ∃ s : U ≅ V, ∀ E F : P.FullSubcategory,
      s.app (q.obj E.obj, q.obj F.obj) = e.app (E, F))
  (hext : ∀ {U V : D × D ⥤ D} (s s' : U ≅ V),
    (∀ E F : P.FullSubcategory, s.app (q.obj E.obj, q.obj F.obj) =
      s'.app (q.obj E.obj, q.obj F.obj)) → s = s')
include hshift hex hext in
private theorem descendTensorShiftAPI (a b : ℤ)
    (c : ((shiftFunctor A a).prod (shiftFunctor A b)) ⋙ t ≅
      t ⋙ shiftFunctor A (a + b)) :
    ∃! s : ((shiftFunctor D a).prod (shiftFunctor D b)) ⋙ T ≅
        T ⋙ shiftFunctor D (a + b),
      TensorShiftNormalization q P t T r a b c s := by
  let S (n : ℤ) : P.FullSubcategory ⥤ P.FullSubcategory := P.lift
    (P.ι ⋙ shiftFunctor _ n) (fun E ↦
      hshift E n)
  let e : ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ ((shiftFunctor _ a).prod (shiftFunctor _ b)) ⋙ T ≅
      ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ T ⋙ shiftFunctor _ (a + b) :=
    SheafOfModules.DerivedTensorConstraints.genericShiftConjugate P.ι
    ((P.ι.prod P.ι) ⋙ t) q T S
    (fun n ↦ isoWhiskerLeft P.ι (q.commShiftIso n))
    r a b (isoWhiskerLeft (P.ι.prod P.ι) c)
  obtain ⟨s, hs⟩ := hex _ _ e
  have he (E F : A)
      (hE : P E) (hF : P F) :
      r.hom.app ((S a).obj ⟨E,hE⟩,(S b).obj ⟨F,hF⟩) ≫
        T.map (Prod.mkHom ((q.commShiftIso a).hom.app E)
          ((q.commShiftIso b).hom.app F)) ≫
        s.hom.app (q.obj E,q.obj F) =
      q.map (c.app (E, F)).hom ≫
        (q.commShiftIso (a + b)).hom.app _ ≫
        (shiftFunctor _ (a + b)).map (r.hom.app (⟨E,hE⟩,⟨F,hF⟩)) := by
    have h := congrArg Iso.hom (hs ⟨E,hE⟩ ⟨F,hF⟩)
    change s.hom.app (q.obj E,q.obj F) =
      e.hom.app (⟨E,hE⟩,⟨F,hF⟩) at h
    rw [h]
    dsimp only [e]
    erw [SheafOfModules.DerivedTensorConstraints.genericShiftConjugate_hom_app]
    simp only [isoWhiskerLeft_inv, whiskerLeft_app]
    erw [← T.map_comp_assoc]
    have hi : Prod.mkHom ((q.commShiftIso a).hom.app E)
        ((q.commShiftIso b).hom.app F) ≫
        Prod.mkHom ((q.commShiftIso a).inv.app E)
          ((q.commShiftIso b).inv.app F) = 𝟙 _ :=
      (Iso.prod ((q.commShiftIso a).app E)
        ((q.commShiftIso b).app F)).hom_inv_id
    erw [hi]
    erw [T.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc]
    rfl
  refine ⟨s, (fun E F hE hF ↦ ⟨_,_,he E F hE hF⟩), ?_⟩
  intro s' hs'
  apply hext
  rintro ⟨E,hE⟩ ⟨F,hF⟩
  apply Iso.ext
  obtain ⟨hEa,hFb,h⟩ := hs' E F hE hF
  have hi : IsIso (Prod.mkHom ((q.commShiftIso a).hom.app E)
      ((q.commShiftIso b).hom.app F)) :=
    (Iso.prod ((q.commShiftIso a).app E)
      ((q.commShiftIso b).app F)).isIso_hom
  apply (cancel_epi (T.map (Prod.mkHom
    ((q.commShiftIso a).hom.app E)
    ((q.commShiftIso b).hom.app F)))).1
  apply (cancel_epi (r.hom.app (⟨E⟦a⟧,hEa⟩,⟨F⟦b⟧,hFb⟩))).1
  exact h.trans (he E F hE hF).symm


end GenericShiftDescent
set_option backward.isDefEq.respectTransparency true

section
variable {A B Z : Type*} [Category* A] [Category* B] [Category* Z]
  [HasShift A ℤ] [HasShift B ℤ] [HasShift Z ℤ]
  (T : A ⥤ B ⥤ Z) [∀ X, (T.obj X).CommShift ℤ]
  [∀ X Y (f : X ⟶ Y), NatTrans.CommShift (T.map f) ℤ]

/-- Extract the shift in the second input by its functorial shift comparison. -/
def tensorRightShift (b : ℤ) :
    ((𝟭 A).prod (shiftFunctor B b)) ⋙ Functor.uncurry.obj T ≅
      Functor.uncurry.obj T ⋙ shiftFunctor Z b := by
  refine NatIso.ofComponents (fun E ↦ ((T.obj E.1).commShiftIso b).app E.2) ?_
  intro E F f
  dsimp [Functor.uncurry, CategoryTheory.Functor.prod, Functor.comp]
  rw [Category.assoc]
  erw [((T.obj F.1).commShiftIso b).hom.naturality]
  rw [← Category.assoc, ← NatTrans.shift_app_comm]
  simp only [Functor.comp_map, CategoryTheory.Functor.map_comp, Category.assoc]
end

section
variable {A B Z : Type*} [Category* A] [Category* B] [Category* Z]
  [HasShift A ℤ] [HasShift B ℤ] [HasShift Z ℤ]
  (T : A ⥤ B ⥤ Z) [∀ X, (T.flip.obj X).CommShift ℤ]
  [∀ X Y (f : X ⟶ Y), NatTrans.CommShift (T.flip.map f) ℤ]

/-- Extract the shift in the first input by its functorial shift comparison. -/
def tensorLeftShift (a : ℤ) :
    ((shiftFunctor A a).prod (𝟭 B)) ⋙ Functor.uncurry.obj T ≅
      Functor.uncurry.obj T ⋙ shiftFunctor Z a := by
  refine NatIso.ofComponents (fun E ↦ ((T.flip.obj E.2).commShiftIso a).app E.1) ?_
  intro E F f
  dsimp [Functor.uncurry, CategoryTheory.Functor.prod, Functor.comp]
  rw [Category.assoc]
  erw [← NatTrans.shift_app_comm (T.flip.map f.2) a F.1]
  rw [← Category.assoc]
  erw [((T.flip.obj E.2).commShiftIso a).hom.naturality]
  simp only [Functor.comp_map, CategoryTheory.Functor.map_comp, Category.assoc]
  rfl
end

section
variable {A B Z : Type*} [Category* A] [Category* B] [Category* Z]
  [HasShift A ℤ] [HasShift B ℤ] [HasShift Z ℤ]
  (T : A ⥤ B ⥤ Z) [∀ X, (T.obj X).CommShift ℤ]
  [∀ X Y (f : X ⟶ Y), NatTrans.CommShift (T.map f) ℤ]
  [∀ X, (T.flip.obj X).CommShift ℤ]
  [∀ X Y (f : X ⟶ Y), NatTrans.CommShift (T.flip.map f) ℤ]

/-- Extract two shifts, moving the second shift before the first. -/
def tensorPairShift (a b : ℤ) :
    ((shiftFunctor A a).prod (shiftFunctor B b)) ⋙ Functor.uncurry.obj T ≅
      Functor.uncurry.obj T ⋙ shiftFunctor Z (a + b) :=
  isoWhiskerLeft ((shiftFunctor A a).prod (𝟭 B)) (tensorRightShift T b) ≪≫
    isoWhiskerRight (tensorLeftShift T a) (shiftFunctor Z b) ≪≫
    isoWhiskerLeft (Functor.uncurry.obj T) (shiftFunctorAdd Z a b).symm

end

section
variable {A B Z : Type*} [Category* A] [Category* B] [Category* Z]
  [Preadditive A] [Preadditive B] [Preadditive Z]
  (F : A ⥤ B ⥤ Z) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ E : CochainComplex A ℤ, ∀ G : CochainComplex B ℤ,
    CochainComplex.HasMapBifunctor E G F]

@[irreducible]
def totalTensorPairShift (a b : ℤ) :
    ((shiftFunctor (CochainComplex A ℤ) a).prod
      (shiftFunctor (CochainComplex B ℤ) b)) ⋙ Functor.uncurry.obj F.map₂CochainComplex ≅
    Functor.uncurry.obj F.map₂CochainComplex ⋙ shiftFunctor _ (a + b) :=
  tensorPairShift F.map₂CochainComplex a b

end



section PullbackPredicates
variable {D : Type u₁} [Category.{v₁} D] [HasShift D ℤ]
  {E : Type u₂} [Category.{v₂} E] [HasShift E ℤ]
  (T : D × D ⥤ D) (TS : E × E ⥤ E) (U : D ⥤ E) [U.CommShift ℤ]
  (tR : ∀ a b : ℤ, ((shiftFunctor D a).prod (shiftFunctor D b)) ⋙ T ≅
    T ⋙ shiftFunctor D (a + b))
  (tS : ∀ a b : ℤ, ((shiftFunctor E a).prod (shiftFunctor E b)) ⋙ TS ≅
    TS ⋙ shiftFunctor E (a + b))

/-- The associator, symmetry and shift equations for a tensor comparison.
Source: Stacks 03EL, 07A4 and 0FPQ
(blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def GenericTensorPullbackCoherence
    (αR : (T.prod (𝟭 D)) ⋙ T ≅
      CategoryTheory.prod.associator D D D ⋙ ((𝟭 D).prod T) ⋙ T)
    (σR : T ≅ CategoryTheory.Prod.swap D D ⋙ T)
    (αS : (TS.prod (𝟭 E)) ⋙ TS ≅
      CategoryTheory.prod.associator E E E ⋙ ((𝟭 E).prod TS) ⋙ TS)
    (σS : TS ≅ CategoryTheory.Prod.swap E E ⋙ TS)
    (μ : T ⋙ U ≅ (U.prod U) ⋙ TS) : Prop :=
  (∀ X Y Z : D,
    U.map (αR.hom.app ((X,Y),Z)) ≫ μ.hom.app (X,T.obj (Y,Z)) ≫
      TS.map (Prod.mkHom (𝟙 (U.obj X)) (μ.hom.app (Y,Z))) =
    μ.hom.app (T.obj (X,Y),Z) ≫
      TS.map (Prod.mkHom (μ.hom.app (X,Y)) (𝟙 (U.obj Z))) ≫
      αS.hom.app ((U.obj X,U.obj Y),U.obj Z)) ∧
  (∀ X Y : D,
    U.map (σR.hom.app (X,Y)) ≫ μ.hom.app (Y,X) =
      μ.hom.app (X,Y) ≫ σS.hom.app (U.obj X,U.obj Y)) ∧
  ∀ (a b : ℤ) (X Y : D),
    U.map ((tR a b).hom.app (X,Y)) ≫
      (U.commShiftIso (a + b)).hom.app (T.obj (X,Y)) ≫
      (shiftFunctor E (a + b)).map (μ.hom.app (X,Y)) =
    μ.hom.app (X⟦a⟧,Y⟦b⟧) ≫
      TS.map (Prod.mkHom ((U.commShiftIso a).hom.app X)
        ((U.commShiftIso b).hom.app Y)) ≫
      (tS a b).hom.app (U.obj X,U.obj Y)

end PullbackPredicates

section BinaryNormalization
variable {A : Type u₁} [Category.{v₁} A] [HasShift A ℤ]
  {D : Type u₂} [Category.{v₂} D] [HasShift D ℤ]
  (q : A ⥤ D) [q.CommShift ℤ] (P : ObjectProperty A)
  (t : A × A ⥤ A) (T : D × D ⥤ D)
  (r : (P.ι.prod P.ι) ⋙ t ⋙ q ≅ ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ T)

/-- The representative normalization of a tensor symmetry.
Source: Stacks 0FPT (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def TensorSymmetryNormalization
    (H : ∀ E F : A, (t.obj (E, F) ≅ t.obj (F, E)) → Prop)
    (σ : T ≅ CategoryTheory.Prod.swap D D ⋙ T) : Prop :=
  ∀ (E F : A) (hE : P E) (hF : P F),
    ∃ χ : t.obj (E, F) ≅ t.obj (F, E), H E F χ ∧
      r.hom.app (⟨E, hE⟩, ⟨F, hF⟩) ≫ σ.hom.app (q.obj E, q.obj F) =
        q.map χ.hom ≫ r.hom.app (⟨F, hF⟩, ⟨E, hE⟩)
end BinaryNormalization

private theorem descendTensorSwapNormalized
    {A : Type u₁} [Category.{v₁} A] {D : Type u₂} [Category.{v₂} D]
    (q : A ⥤ D) (P : ObjectProperty A) (t : A × A ⥤ A) (T : D × D ⥤ D)
    (r : (P.ι.prod P.ι) ⋙ t ⋙ q ≅ ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ T)
    (c : t ≅ CategoryTheory.Prod.swap A A ⋙ t)
    (H : ∀ E F : A, (t.obj (E, F) ≅ t.obj (F, E)) → Prop)
    (hc : ∀ E F, H E F (c.app (E, F)))
    (huniq : ∀ (E F : A) (χ χ' : t.obj (E, F) ≅ t.obj (F, E)),
      H E F χ → H E F χ' → χ = χ')
    (hex : ∀ (U V : D × D ⥤ D)
      (e : ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ U ≅
        ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ V),
      ∃ s : U ≅ V, ∀ E F : P.FullSubcategory,
        s.app (q.obj E.obj, q.obj F.obj) = e.app (E, F))
    (hext : ∀ {U V : D × D ⥤ D} (s s' : U ≅ V),
      (∀ E F : P.FullSubcategory, s.app (q.obj E.obj, q.obj F.obj) =
        s'.app (q.obj E.obj, q.obj F.obj)) → s = s') :
    ∃! σ : T ≅ CategoryTheory.Prod.swap D D ⋙ T,
      TensorSymmetryNormalization q P t T r H σ := by
  obtain ⟨σ, hs, hu⟩ := descendTensorSwap q P t T r c hex hext
  refine ⟨σ, ?_, ?_⟩
  · intro E F hE hF
    exact ⟨c.app (E, F), hc E F, hs E F hE hF⟩
  · intro σ' hσ'
    apply hu σ'
    intro E F hE hF
    obtain ⟨χ, hχ, h⟩ := hσ' E F hE hF
    have he := huniq E F χ (c.app (E, F)) hχ (hc E F)
    subst χ
    exact h


section NormalizationPredicates
variable {A : Type u₁} [Category.{v₁} A] {D : Type u₂} [Category.{v₂} D]
  (q : A ⥤ D) (P : ObjectProperty A) (t : A × A ⥤ A) (T : D × D ⥤ D)
  (r : (P.ι.prod P.ι) ⋙ t ⋙ q ≅ ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ T)

/-- A tensor associator is normalized by its representative square.
Source: Stacks 0FPQ/0FPT (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def TensorAssociatorNormalization
    (H : ∀ E F G : A, (t.obj (t.obj (E, F), G) ≅ t.obj (E, t.obj (F, G))) → Prop)
    (α : (T.prod (𝟭 D)) ⋙ T ≅
      CategoryTheory.prod.associator D D D ⋙ ((𝟭 D).prod T) ⋙ T) : Prop :=
  ∀ (E F G : A) (hE : P E) (hF : P F) (hG : P G),
    ∃ (hEF : P (t.obj (E, F))) (hFG : P (t.obj (F, G)))
      (χ : t.obj (t.obj (E, F), G) ≅ t.obj (E, t.obj (F, G))),
      H E F G χ ∧
      r.hom.app (⟨_, hEF⟩, ⟨G, hG⟩) ≫
        T.map (Prod.mkHom (r.hom.app (⟨E, hE⟩, ⟨F, hF⟩)) (𝟙 (q.obj G))) ≫
        α.hom.app ((q.obj E, q.obj F), q.obj G) =
      q.map χ.hom ≫ r.hom.app (⟨E, hE⟩, ⟨_, hFG⟩) ≫
        T.map (Prod.mkHom (𝟙 (q.obj E)) (r.hom.app (⟨F, hF⟩, ⟨G, hG⟩)))
end NormalizationPredicates

/-- A tensor functor with its natural resolving comparison. -/
structure ResolvingTensorModel
    {A : Type u₁} [Category.{v₁} A] {D : Type u₂} [Category.{v₂} D]
    (q : A ⥤ D) (P : ObjectProperty A) (t : A × A ⥤ A) where
  tensor : D × D ⥤ D
  representative : (P.ι.prod P.ι) ⋙ t ⋙ q ≅
    ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ tensor

private theorem descendTensorAssociatorNormalized
    {A : Type u₁} [Category.{v₁} A] {D : Type u₂} [Category.{v₂} D]
    (q : A ⥤ D) (P : ObjectProperty A) (t : A × A ⥤ A) (T : D × D ⥤ D)
    (r : (P.ι.prod P.ι) ⋙ t ⋙ q ≅ ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ T)
    (hclosed : ∀ E F : P.FullSubcategory, P (t.obj (E.obj, F.obj)))
    (c : (t.prod (𝟭 A)) ⋙ t ≅
      CategoryTheory.prod.associator A A A ⋙ ((𝟭 A).prod t) ⋙ t)
    (H : ∀ E F G : A, (t.obj (t.obj (E, F), G) ≅ t.obj (E, t.obj (F, G))) → Prop)
    (hc : ∀ E F G, H E F G (c.app ((E, F), G)))
    (huniq : ∀ (E F G : A) (χ χ' : t.obj (t.obj (E, F), G) ≅
        t.obj (E, t.obj (F, G))), H E F G χ → H E F G χ' → χ = χ')
    (hex : ∀ (U V : (D × D) × D ⥤ D)
      (e : (((P.ι ⋙ q).prod (P.ι ⋙ q)).prod (P.ι ⋙ q)) ⋙ U ≅
        (((P.ι ⋙ q).prod (P.ι ⋙ q)).prod (P.ι ⋙ q)) ⋙ V),
      ∃ s : U ≅ V, ∀ E F G : P.FullSubcategory,
        s.app ((q.obj E.obj, q.obj F.obj), q.obj G.obj) = e.app ((E, F), G))
    (hext : ∀ {U V : (D × D) × D ⥤ D} (s s' : U ≅ V),
      (∀ E F G : P.FullSubcategory,
        s.app ((q.obj E.obj, q.obj F.obj), q.obj G.obj) =
          s'.app ((q.obj E.obj, q.obj F.obj), q.obj G.obj)) → s = s') :
    ∃! α : (T.prod (𝟭 D)) ⋙ T ≅
        CategoryTheory.prod.associator D D D ⋙ ((𝟭 D).prod T) ⋙ T,
      TensorAssociatorNormalization q P t T r H α := by
  let m : P.FullSubcategory × P.FullSubcategory ⥤ P.FullSubcategory :=
    P.lift ((P.ι.prod P.ι) ⋙ t) (fun E ↦ hclosed E.1 E.2)
  let l := isoWhiskerLeft (m.prod (𝟭 _)) r ≪≫
    isoWhiskerRight (NatIso.prod r (Iso.refl (P.ι ⋙ q))) T
  let rr := isoWhiskerLeft (CategoryTheory.prod.associator
      P.FullSubcategory P.FullSubcategory P.FullSubcategory)
    (isoWhiskerLeft ((𝟭 _).prod m) r ≪≫
      isoWhiskerRight (NatIso.prod (Iso.refl (P.ι ⋙ q)) r) T)
  let e := l.symm ≪≫
    isoWhiskerRight (isoWhiskerLeft ((P.ι.prod P.ι).prod P.ι) c) q ≪≫ rr
  obtain ⟨α, hα⟩ := hex ((T.prod (𝟭 D)) ⋙ T)
    (CategoryTheory.prod.associator D D D ⋙ ((𝟭 D).prod T) ⋙ T) e
  have hn (E F G : P.FullSubcategory) :
      r.hom.app (m.obj (E, F), G) ≫
        T.map (Prod.mkHom (r.hom.app (E, F)) (𝟙 (q.obj G.obj))) ≫
        α.hom.app ((q.obj E.obj, q.obj F.obj), q.obj G.obj) =
      q.map (c.hom.app ((E.obj, F.obj), G.obj)) ≫
        r.hom.app (E, m.obj (F, G)) ≫
        T.map (Prod.mkHom (𝟙 (q.obj E.obj)) (r.hom.app (F, G))) := by
    have ha := congrArg Iso.hom (hα E F G)
    change α.hom.app ((q.obj E.obj, q.obj F.obj), q.obj G.obj) = _ at ha
    rw [ha]
    rw [← Category.assoc]
    change l.hom.app ((E, F), G) ≫ e.hom.app ((E, F), G) = _
    simp only [e, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Iso.hom_inv_id_app_assoc, isoWhiskerLeft_hom, isoWhiskerRight_hom,
      whiskerLeft_app, whiskerRight_app]
    rfl
  refine ⟨α, ?_, ?_⟩
  · intro E F G hE hF hG
    exact ⟨hclosed ⟨E, hE⟩ ⟨F, hF⟩, hclosed ⟨F, hF⟩ ⟨G, hG⟩,
      c.app ((E, F), G), hc E F G, hn ⟨E, hE⟩ ⟨F, hF⟩ ⟨G, hG⟩⟩
  · intro α' hα'
    apply hext
    rintro ⟨E, hE⟩ ⟨F, hF⟩ ⟨G, hG⟩
    apply Iso.ext
    obtain ⟨hEF, hFG, χ, hχ, h⟩ := hα' E F G hE hF hG
    have he := huniq E F G χ (c.app ((E, F), G)) hχ (hc E F G)
    subst χ
    have : IsIso (Prod.mkHom (r.hom.app (⟨E, hE⟩, ⟨F, hF⟩)) (𝟙 (q.obj G))) :=
      (Iso.prod (r.app (⟨E, hE⟩, ⟨F, hF⟩)) (Iso.refl (q.obj G))).isIso_hom
    apply (cancel_epi (T.map (Prod.mkHom
      (r.hom.app (⟨E, hE⟩, ⟨F, hF⟩)) (𝟙 (q.obj G))))).1
    apply (cancel_epi (r.hom.app (⟨t.obj (E, F), hEF⟩, ⟨G, hG⟩))).1
    exact h.trans (hn ⟨E, hE⟩ ⟨F, hF⟩ ⟨G, hG⟩).symm

section ComplexFormulaPredicates
variable {A : Type u₁} [Category.{v₁} A] [Preadditive A]
  [HasZeroObject A] [MonoidalCategory A] [MonoidalPreadditive A] [BraidedCategory A]
  [∀ E F : CochainComplex A ℤ, HomologicalComplex.HasTensor E F]
  [∀ E F G : CochainComplex A ℤ, HomologicalComplex.HasGoodTensor₁₂ E F G]

/-- Signed swap on total complexes, characterized on every summand. These equations
specify an actual map, including its sign; existence is part of the derived normalization.
Source: Stacks 0FPQ (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def ComplexTensorSwapFormula (E F : CochainComplex A ℤ)
    (χ : (HomologicalComplex.tensorObj E F) ≅ (HomologicalComplex.tensorObj F E)) : Prop :=
  ∀ p q : ℤ,
    CochainComplex.ιMapBifunctor E F (curriedTensor A) p q (p + q) rfl ≫
      χ.hom.f (p + q) =
    ((-1 : ℤ) ^ Int.natAbs (p * q)) •
      ((β_ (E.X p) (F.X q)).hom ≫
        CochainComplex.ιMapBifunctor F E (curriedTensor A) q p (p + q)
          (add_comm q p))

/-- The unsigned associator is fixed on triple total summands.
Source: Stacks 0FPQ (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def ComplexTensorAssociatorFormula (E F G : CochainComplex A ℤ)
    (χ : (HomologicalComplex.tensorObj (HomologicalComplex.tensorObj E F) G) ≅
      (HomologicalComplex.tensorObj E (HomologicalComplex.tensorObj F G))) : Prop :=
  ∀ p q r : ℤ,
    ((curriedTensor A).map
      (CochainComplex.ιMapBifunctor E F (curriedTensor A) p q (p + q) rfl)).app _ ≫
      CochainComplex.ιMapBifunctor ((HomologicalComplex.tensorObj E F)) G
        (curriedTensor A) (p + q) r ((p + q) + r) rfl ≫
      χ.hom.f ((p + q) + r) =
    (α_ (E.X p) (F.X q) (G.X r)).hom ≫
      ((curriedTensor A).obj (E.X p)).map
        (CochainComplex.ιMapBifunctor F G (curriedTensor A) q r (q + r) rfl) ≫
      CochainComplex.ιMapBifunctor E ((HomologicalComplex.tensorObj F G))
        (curriedTensor A) p (q + r) ((p + q) + r) (add_assoc p q r).symm

end ComplexFormulaPredicates

section
variable {A : Type u₁} [Category.{v₁} A] [Preadditive A]
  [HasZeroObject A] [MonoidalCategory A] [MonoidalPreadditive A]
  [∀ E F : GradedObject ℤ A, GradedObject.HasTensor E F]
  [∀ E F G : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor E F G]
  [∀ E F G : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ E F G]

private theorem descendTotalAssociator
    {D : Type u₂} [Category.{v₂} D] (q : CochainComplex A ℤ ⥤ D)
    (P : ObjectProperty (CochainComplex A ℤ)) (T : D × D ⥤ D)
    (r : (P.ι.prod P.ι) ⋙ Functor.uncurry.obj (curriedTensor A).map₂CochainComplex ⋙ q ≅
      ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ T)
    (hc : ∀ E F : P.FullSubcategory, P (HomologicalComplex.tensorObj E.obj F.obj))
    (hex : ∀ (U V : (D × D) × D ⥤ D)
      (e : (((P.ι ⋙ q).prod (P.ι ⋙ q)).prod (P.ι ⋙ q)) ⋙ U ≅
        (((P.ι ⋙ q).prod (P.ι ⋙ q)).prod (P.ι ⋙ q)) ⋙ V),
      ∃ s : U ≅ V, ∀ E F G : P.FullSubcategory,
        s.app ((q.obj E.obj, q.obj F.obj), q.obj G.obj) = e.app ((E, F), G))
    (hext : ∀ {U V : (D × D) × D ⥤ D} (s s' : U ≅ V),
      (∀ E F G : P.FullSubcategory,
        s.app ((q.obj E.obj, q.obj F.obj), q.obj G.obj) =
          s'.app ((q.obj E.obj, q.obj F.obj), q.obj G.obj)) → s = s') :
    ∃! α : (T.prod (𝟭 D)) ⋙ T ≅
        CategoryTheory.prod.associator D D D ⋙ ((𝟭 D).prod T) ⋙ T,
      TensorAssociatorNormalization q P
        (Functor.uncurry.obj (curriedTensor A).map₂CochainComplex) T r
        (ComplexTensorAssociatorFormula (A := A)) α := by
  let t := Functor.uncurry.obj (curriedTensor A).map₂CochainComplex
  let c : (t.prod (𝟭 _)) ⋙ t ≅
      CategoryTheory.prod.associator _ _ _ ⋙ ((𝟭 _).prod t) ⋙ t := by
    have hm {E E' F F' : CochainComplex A ℤ} (f : E ⟶ E') (g : F ⟶ F') :
        t.map (Prod.mkHom f g) = HomologicalComplex.tensorHom f g := by
      simp [t, Functor.map₂HomologicalComplex, Functor.uncurry_obj_map,
        HomologicalComplex.mapBifunctorMap, ← HomologicalComplex₂.total.map_comp]
    refine NatIso.ofComponents (F := (t.prod (𝟭 _)) ⋙ t)
      (G := CategoryTheory.prod.associator _ _ _ ⋙ ((𝟭 _).prod t) ⋙ t)
      (fun E ↦ HomologicalComplex.associator E.1.1 E.1.2 E.2) ?_
    intro E F f
    change t.map (Prod.mkHom (t.map (Prod.mkHom f.1.1 f.1.2)) f.2) ≫ _ =
      _ ≫ t.map (Prod.mkHom f.1.1 (t.map (Prod.mkHom f.1.2 f.2)))
    rw [hm, hm, hm, hm]
    apply HomologicalComplex.Hom.ext
    funext n
    exact congrFun (GradedObject.Monoidal.associator_naturality
      f.1.1.f f.1.2.f f.2.f) n
  have hf (E F G : CochainComplex A ℤ) :
      ComplexTensorAssociatorFormula E F G (c.app ((E, F), G)) := by
    change ComplexTensorAssociatorFormula E F G (HomologicalComplex.associator E F G)
    intro p q r
    have h := HomologicalComplex.ι_mapBifunctorAssociatorX_hom
      (MonoidalCategory.curriedAssociatorNatIso A) E F G (.up ℤ) (.up ℤ) (.up ℤ)
      p q r ((p + q) + r) rfl
    rw [HomologicalComplex.mapBifunctor₁₂.ι_eq (curriedTensor A) (curriedTensor A)
      E F G (.up ℤ) (.up ℤ) p q r (p + q) ((p + q) + r) rfl rfl] at h
    rw [HomologicalComplex.mapBifunctor₂₃.ι_eq (curriedTensor A) (curriedTensor A)
      E F G (.up ℤ) (.up ℤ) (.up ℤ) p q r (q + r) ((p + q) + r) rfl
      (add_assoc p q r).symm] at h
    simp only [HomologicalComplex.associator, HomologicalComplex.mapBifunctorAssociator,
      HomologicalComplex.Hom.isoOfComponents, MonoidalCategory.curriedAssociatorNatIso,
      NatIso.ofComponents, CochainComplex.ιMapBifunctor, HomologicalComplex.tensorObj,
      Category.assoc] at h ⊢
    exact h
  have hu (E F G : CochainComplex A ℤ)
      (χ χ' : HomologicalComplex.tensorObj (HomologicalComplex.tensorObj E F) G ≅
        HomologicalComplex.tensorObj E (HomologicalComplex.tensorObj F G))
      (hχ : ComplexTensorAssociatorFormula E F G χ)
      (hχ' : ComplexTensorAssociatorFormula E F G χ') : χ = χ' := by
    apply Iso.ext
    apply HomologicalComplex.Hom.ext
    funext n
    apply HomologicalComplex.mapBifunctor₁₂.hom_ext
      (F₁₂ := curriedTensor A) (G := curriedTensor A)
      (K₁ := E) (K₂ := F) (K₃ := G) (c₁₂ := .up ℤ) (c₄ := .up ℤ)
    intro p q r hn
    change p + q + r = n at hn
    subst n
    erw [HomologicalComplex.mapBifunctor₁₂.ι_eq (curriedTensor A) (curriedTensor A)
      E F G (.up ℤ) (.up ℤ) p q r (p + q) ((p + q) + r) rfl rfl]
    simp only [Category.assoc]
    exact (hχ p q r).trans (hχ' p q r).symm
  exact descendTensorAssociatorNormalized q P _ T r hc c
    (ComplexTensorAssociatorFormula (A := A)) hf hu hex hext

end



namespace SheafOfModules
attribute [local irreducible] DerivedCategory.Q DerivedCategory.Qh
  Functor.mapHomologicalComplex Functor.mapBifunctorHomologicalComplex HomologicalComplex₂.total
  CochainComplex.Monoidal.braiding

/-- The module category on the ringed site. Source: Stacks 03DA
(blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
abbrev ShiftedModuleCategory {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasSheafify J AddCommGrpCat.{max u v}]
    (R : Sheaf J CommRingCat.{max u v}) :=
  CategoryTheory.ringedSiteModules.{max u v}
    ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)

/-- Its unbounded derived category. Source: Stacks 05RR
(blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
abbrev ShiftedDerivedCategory {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasSheafify J AddCommGrpCat.{max u v}]
    (R : Sheaf J CommRingCat.{max u v})
    [HasDerivedCategory.{w} (ShiftedModuleCategory R)] :=
  DerivedCategory (ShiftedModuleCategory R)

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasSheafify J AddCommGrpCat.{max u v}]
  (R : Sheaf J CommRingCat.{max u v})
  [HasDerivedCategory.{w} (ShiftedModuleCategory R)]

/-- Flat-term K-flat resolving complexes. Source: Stacks 06YS and 06YU
(blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def shiftedTensorResolving : ObjectProperty (CochainComplex (ShiftedModuleCategory R) ℤ) :=
  fun E ↦ E.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (E.X n)

/-- The ordinary tensor bifunctor, with the dependency's canonical sheaf tensor.
Source: Stacks 03EK (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def shiftedOrdinaryTensor :=
  @curriedTensor (ShiftedModuleCategory R) _ (monoidalCategory R)

omit [HasDerivedCategory.{w} (ShiftedModuleCategory R)] in
theorem shiftedOrdinaryTensor_additive : (shiftedOrdinaryTensor R).Additive := by
  exact KFlatFixedTensor.tensorAdditive R

omit [HasDerivedCategory.{w} (ShiftedModuleCategory R)] in
theorem shiftedOrdinaryTensor_objAdditive (X : ShiftedModuleCategory R) :
    ((shiftedOrdinaryTensor R).obj X).Additive := by
  exact KFlatFixedTensor.tensorObjAdditive R X

attribute [local instance 4001] shiftedOrdinaryTensor_additive
  shiftedOrdinaryTensor_objAdditive

omit [HasDerivedCategory.{w} (ShiftedModuleCategory R)] in
theorem shiftedOrdinaryTensor_totalExists
    (E F : CochainComplex (ShiftedModuleCategory R) ℤ) :
    CochainComplex.HasMapBifunctor E F (shiftedOrdinaryTensor R) := by
  exact KFlatFixedTensor.tensorHasMapBifunctor R E F

attribute [local instance 4001] shiftedOrdinaryTensor_totalExists

/-- Total tensor, with the differential sign on the second factor.
Source: Stacks 06YM (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def shiftedTotalTensor :=
  Functor.uncurry.obj (shiftedOrdinaryTensor R).map₂CochainComplex

omit [HasDerivedCategory.{w} (ShiftedModuleCategory R)] in
private theorem shiftedTotalTensor_obj
    (E F : CochainComplex (ShiftedModuleCategory R) ℤ) :
    (shiftedTotalTensor R).obj (E, F) =
      CochainComplex.mapBifunctor E F (shiftedOrdinaryTensor R) := rfl

/-- A presentation of the derived tensor by the natural resolving comparison.
This is precisely the tensor and its representative isomorphism from site-derived-tensor
 descent; quantifying over presentations makes the statement independent of this choice.
Source: Stacks 06YU (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
abbrev ShiftedTensorModel :=
  ResolvingTensorModel DerivedCategory.Q (shiftedTensorResolving R) (shiftedTotalTensor R)

/-- The recorded site-derived tensor admits exactly the resolving presentation used here.
This connects the presentation-independent calculus to the dependency's actual bifunctor.
Source: Stacks 06YU (blueprint: lem-pur-shifted-tensor-morphism-calculus).
Proof (Step 3): take the tensor and homotopy representative comparison from
site_derived_tensor_descent_independentCoefficients. Precompose its two comparisons
with the resolving complexes' homotopy quotient and compose with quotientCompQhIso.
The membership equivalence identifies precisely the K-flat flat-term objects.
The resulting natural comparison supplies the displayed model of the recorded tensor. -/
theorem shiftedTensorPublishedModel_exists :
    ∃ T : ShiftedTensorModel R,
      T.tensor = siteDerivedTensorIndependentCoefficients J R := by
  refine ⟨⟨siteDerivedTensorIndependentCoefficients J R, ?_⟩, rfl⟩
  let q : (shiftedTensorResolving R).ι ⋙
      HomotopyCategory.quotient (ShiftedModuleCategory R) (.up ℤ) ⋙
        DerivedCategory.Qh ≅ (shiftedTensorResolving R).ι ⋙ DerivedCategory.Q :=
    isoWhiskerLeft (shiftedTensorResolving R).ι
      (DerivedCategory.quotientCompQhIso (ShiftedModuleCategory R))
  exact isoWhiskerLeft ((shiftedTensorResolving R).ι.prod (shiftedTensorResolving R).ι)
      (isoWhiskerLeft (shiftedTotalTensor R)
        (DerivedCategory.quotientCompQhIso (ShiftedModuleCategory R))).symm ≪≫
    DerivedTensorConstraints.genericPresentationComparison (shiftedTensorResolving R).ι
      (KFlatFixedTensor.selectedTensorPresentation R)
      (fun E ↦ (KFlatFixedTensor.resolvingProperty_spec R _).2 E.property) ≪≫
    isoWhiskerRight (NatIso.prod q q) (siteDerivedTensorIndependentCoefficients J R)

@[irreducible]
def shiftedTensorComplexComparisonNatIso (a b : ℤ) :
    ((shiftFunctor (CochainComplex (ShiftedModuleCategory R) ℤ) a).prod
      (shiftFunctor _ b)) ⋙ shiftedTotalTensor R ≅
    shiftedTotalTensor R ⋙ shiftFunctor _ (a + b) :=
  totalTensorPairShift (shiftedOrdinaryTensor R) a b

/-- Move the second shift first, then the first shift. Thus the only sign is
`(-1)^(bp)` with p the degree in E[a], exactly the node's convention.
Source: Stacks sign rules, item-shift-tensor
(blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def shiftedTensorComplexComparison
    (E F : CochainComplex (ShiftedModuleCategory R) ℤ) (a b : ℤ) :
    (shiftedTotalTensor R).obj (E⟦a⟧, F⟦b⟧) ≅
      ((shiftedTotalTensor R).obj (E, F))⟦a + b⟧ :=
  (shiftedTensorComplexComparisonNatIso R a b).app (E, F)

variable (T : ShiftedTensorModel R)

/-- Normalization of t on every resolving model, with localization's shift comparisons.
Source: Stacks 06YU and sign rules (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def IsCanonicalShiftComparison (a b : ℤ)
    (t : ((CategoryTheory.shiftFunctor (ShiftedDerivedCategory R) a).prod
      (CategoryTheory.shiftFunctor (ShiftedDerivedCategory R) b) ⋙ T.tensor) ≅
      T.tensor ⋙ CategoryTheory.shiftFunctor _ (a + b)) : Prop :=
  TensorShiftNormalization DerivedCategory.Q (shiftedTensorResolving R)
    (shiftedTotalTensor R) T.tensor T.representative a b
    (shiftedTensorComplexComparisonNatIso R a b) t

attribute [local irreducible] TensorShiftNormalization TensorSymmetryNormalization
  TensorAssociatorNormalization GenericTensorPullbackCoherence

attribute [local irreducible] siteDerivedTensorIndependentCoefficients

private theorem shiftedModelShift_closed
    (E : (shiftedTensorResolving R).FullSubcategory) (n : ℤ) :
    shiftedTensorResolving R (E.obj⟦n⟧) := by
  exact (DerivedTensorConstraints.derived_tensor_model_closure R).2.1 ⟨E.obj, E.property⟩ n

/-- The canonical comparison is uniquely determined by the resolving square.
Source: Stacks 06YU; proof Steps 1--3 of the node
(blueprint: lem-pur-shifted-tensor-morphism-calculus).
Proof: the two complex shift isomorphisms give the coefficient (-1)^(bp), and are natural.
Shifts preserve K-flatness and flat terms (Step 2). Transport through the representative
comparison and extend the resulting transformation and its inverse by the unique-extension
clause of site-derived-tensor descent (Step 3). Uniqueness proves the inverse equations
and the asserted uniqueness. -/
theorem shiftedTensorCanonicalComparison_exists (a b : ℤ) :
    ∃! t : ((CategoryTheory.shiftFunctor (ShiftedDerivedCategory R) a).prod
      (CategoryTheory.shiftFunctor (ShiftedDerivedCategory R) b) ⋙ T.tensor) ≅
      T.tensor ⋙ CategoryTheory.shiftFunctor _ (a + b),
      IsCanonicalShiftComparison R T a b t := by
  exact descendTensorShiftAPI DerivedCategory.Q (shiftedTensorResolving R)
    (shiftedTotalTensor R) T.tensor T.representative (shiftedModelShift_closed R)
    (DerivedTensorConstraints.extendBinary R)
    (fun _ _ h ↦ DerivedTensorConstraints.binary_iso_ext R _ _ h)
    a b (shiftedTensorComplexComparisonNatIso R a b)


/-- The comparison fixed by the actual resolving square, not a free parameter.
Source: Stacks 06YU (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def shiftedTensorCanonicalComparison (a b : ℤ) :
    ((shiftFunctor (ShiftedDerivedCategory R) a).prod (shiftFunctor _ b)) ⋙ T.tensor ≅
      T.tensor ⋙ shiftFunctor _ (a + b) :=
  (shiftedTensorCanonicalComparison_exists R T a b).exists.choose

attribute [local irreducible] shiftedTensorCanonicalComparison

/-- Signed swap on total complexes, characterized on every summand. These equations
specify an actual map, including its sign; existence is part of the derived normalization.
Source: Stacks 0FPQ (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def IsSignedComplexSwap (E F : CochainComplex (ShiftedModuleCategory R) ℤ)
    (χ : (shiftedTotalTensor R).obj (E, F) ≅ (shiftedTotalTensor R).obj (F, E)) : Prop :=
  letI := monoidalCategory R
  letI := symmetricCategory R
  letI := CanonicalTensorPullbackOfUniverses.ringedTensorPreadditive R
  ComplexTensorSwapFormula E F χ

/-- Derived symmetry is the image of the signed swap on K-flat representatives.
Source: Stacks 0FPQ and 06YU (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def IsCanonicalDerivedTensorSymmetry
    (σ : T.tensor ≅ CategoryTheory.Prod.swap _ _ ⋙ T.tensor) : Prop :=
  TensorSymmetryNormalization DerivedCategory.Q (shiftedTensorResolving R)
    (shiftedTotalTensor R) T.tensor T.representative (IsSignedComplexSwap R) σ

private def shiftedComplexSwap
    (E F : CochainComplex (ShiftedModuleCategory R) ℤ) :
    (shiftedTotalTensor R).obj (E, F) ≅ (shiftedTotalTensor R).obj (F, E) :=
  letI := monoidalCategory R
  letI := symmetricCategory R
  letI := CanonicalTensorPullbackOfUniverses.ringedTensorPreadditive R
  totalComplexSwap E F

omit [HasDerivedCategory.{w} (ShiftedModuleCategory R)] in
private theorem shiftedComplexSwap_signed (E F : CochainComplex (ShiftedModuleCategory R) ℤ) :
    IsSignedComplexSwap R E F (shiftedComplexSwap R E F) := by
  let := monoidalCategory R
  let := symmetricCategory R
  let := CanonicalTensorPullbackOfUniverses.ringedTensorPreadditive R
  intro p q
  exact totalComplexSwap_signed E F p q

omit [HasDerivedCategory.{w} (ShiftedModuleCategory R)] in
private theorem shiftedComplexSwap_unique (E F : CochainComplex (ShiftedModuleCategory R) ℤ)
    (χ χ' : (shiftedTotalTensor R).obj (E, F) ≅ (shiftedTotalTensor R).obj (F, E))
    (hχ : IsSignedComplexSwap R E F χ) (hχ' : IsSignedComplexSwap R E F χ') : χ = χ' := by
  apply Iso.ext
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  subst n
  exact (hχ p q).trans (hχ' p q).symm

/-- Existence and uniqueness of the signed derived symmetry.
Source: Stacks 0FPQ and 06YU (blueprint: lem-pur-shifted-tensor-morphism-calculus).
Proof (Step 3): define the swap by its summand equations. The differential coefficients
of y tensor dx agree modulo 2, as do those of dy tensor x. The reverse swap is its inverse.
It is natural; descend it and its inverse using the unique-extension clause of tensor descent.
The summand equations determine the chain map and descent determines the natural isomorphism. -/
theorem derivedTensorSymmetry_exists :
    ∃! σ : T.tensor ≅ CategoryTheory.Prod.swap _ _ ⋙ T.tensor,
      IsCanonicalDerivedTensorSymmetry R T σ := by
  let := monoidalCategory R
  let := symmetricCategory R
  let := CanonicalTensorPullbackOfUniverses.ringedTensorPreadditive R
  let c : shiftedTotalTensor R ≅ CategoryTheory.Prod.swap _ _ ⋙ shiftedTotalTensor R :=
    totalSwapNatIso (shiftedComplexSwap R) (shiftedComplexSwap_signed R)
  exact descendTensorSwapNormalized DerivedCategory.Q (shiftedTensorResolving R)
    (shiftedTotalTensor R) T.tensor T.representative c (IsSignedComplexSwap R)
    (by
      intro E F
      have he : c.app (E, F) = shiftedComplexSwap R E F := by
        apply Iso.ext
        exact totalSwapNatIso_hom_app (shiftedComplexSwap R)
          (shiftedComplexSwap_signed R) E F
      rw [he]
      exact shiftedComplexSwap_signed R E F)
    (shiftedComplexSwap_unique R) (DerivedTensorConstraints.extendBinary R)
    (fun _ _ h ↦ DerivedTensorConstraints.binary_iso_ext R _ _ h)


/-- Canonical Koszul symmetry, fixed by the signed representative equations.
Source: Stacks 0FPQ (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def derivedTensorSymmetry :
    T.tensor ≅ CategoryTheory.Prod.swap _ _ ⋙ T.tensor :=
  (derivedTensorSymmetry_exists R T).exists.choose

attribute [local irreducible] derivedTensorSymmetry

/-- B is tensor of the two maps followed by the canonical shift comparison.
Source: Stacks 0FPL/0FPM (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def shiftedTensorB (a b : ℤ) (P Q K L : ShiftedDerivedCategory R)
    (f : P ⟶ K⟦a⟧) (g : Q ⟶ L⟦b⟧) :
    T.tensor.obj (P, Q) ⟶ (T.tensor.obj (K, L))⟦a + b⟧ :=
  T.tensor.map (Prod.mkHom f g) ≫
    (shiftedTensorCanonicalComparison R T a b).hom.app (K, L)

/-- The unsigned associator is fixed on triple total summands.
Source: Stacks 0FPQ (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def IsComplexTensorAssociator (E F G : CochainComplex (ShiftedModuleCategory R) ℤ)
    (χ : (shiftedTotalTensor R).obj ((shiftedTotalTensor R).obj (E, F), G) ≅
      (shiftedTotalTensor R).obj (E, (shiftedTotalTensor R).obj (F, G))) : Prop :=
  letI := monoidalCategory R
  letI := CanonicalTensorPullbackOfUniverses.ringedTensorPreadditive R
  ComplexTensorAssociatorFormula E F G χ

/-- The left triple tensor functor. Source: Stacks 0FPQ
(blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
abbrev shiftedTensorLeftTriple := (T.tensor.prod (𝟭 _)) ⋙ T.tensor

/-- The right triple tensor functor. Source: Stacks 0FPQ
(blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
abbrev shiftedTensorRightTriple :=
  CategoryTheory.prod.associator (ShiftedDerivedCategory R) _ _ ⋙
    ((𝟭 _).prod T.tensor) ⋙ T.tensor

/-- The derived associator's full representative square, including tensor closure.
Source: Stacks 0FPQ/0FPT (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def IsCanonicalTensorAssociator
    (α : shiftedTensorLeftTriple R T ≅ shiftedTensorRightTriple R T) : Prop :=
  TensorAssociatorNormalization DerivedCategory.Q (shiftedTensorResolving R)
    (shiftedTotalTensor R) T.tensor T.representative (IsComplexTensorAssociator R) α

/-- The derived associator exists uniquely with its unsigned normalization.
Source: Stacks 0FPQ/0FPT (blueprint: lem-pur-shifted-tensor-morphism-calculus).
Proof (Steps 2--3): tensor preserves sums by its right adjoint, so triple tensor
summands determine the unsigned associator and its inverse. Differential signs are
1, (-1)^p, (-1)^(p+q) on both sides. K-flatness of total tensor follows by applying
K-flatness twice to an acyclic test complex. Tensor products and sums of flat terms
are flat. Extend the representative square and its inverse by tensor descent,
variable by variable. Uniqueness on resolving triples gives uniqueness everywhere. -/
theorem derivedTensorAssociator_exists :
    ∃! α : shiftedTensorLeftTriple R T ≅ shiftedTensorRightTriple R T,
      IsCanonicalTensorAssociator R T α := by
  let := monoidalCategory R
  let := CanonicalTensorPullbackOfUniverses.ringedTensorPreadditive R
  exact descendTotalAssociator DerivedCategory.Q (shiftedTensorResolving R)
    T.tensor T.representative (DerivedTensorConstraints.derived_tensor_model_closure R).1
    (DerivedTensorConstraints.extendTernary R)
    (fun _ _ h ↦ DerivedTensorConstraints.ternary_iso_ext R _ _ h)

/-- Canonical associator, with no arbitrary associator parameter.
Source: Stacks 0FPQ (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def derivedTensorAssociator :
    shiftedTensorLeftTriple R T ≅ shiftedTensorRightTriple R T :=
  (derivedTensorAssociator_exists R T).exists.choose

attribute [local irreducible] derivedTensorAssociator

/-- A module sheaf in degree zero. Source: Stacks 06YU
(blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
abbrev shiftedDegreeZero (P : ShiftedModuleCategory R) : ShiftedDerivedCategory R :=
  (DerivedCategory.singleFunctor _ 0).obj P

/-- Both additivity equations for flat degree-zero sources.
Source: Stacks 0FPL/0FPM (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def ShiftedTensorAdditivityClause (a b : ℤ) : Prop :=
  ∀ (P Q : ShiftedModuleCategory R), IsFlatOnSite P → IsFlatOnSite Q →
    ∀ (K L : ShiftedDerivedCategory R)
      (f₁ f₂ : shiftedDegreeZero R P ⟶ K⟦a⟧)
      (g₁ g₂ : shiftedDegreeZero R Q ⟶ L⟦b⟧),
      shiftedTensorB R T a b _ _ K L (f₁ + f₂) g₁ =
        shiftedTensorB R T a b _ _ K L f₁ g₁ + shiftedTensorB R T a b _ _ K L f₂ g₁ ∧
      shiftedTensorB R T a b _ _ K L f₁ (g₁ + g₂) =
        shiftedTensorB R T a b _ _ K L f₁ g₁ + shiftedTensorB R T a b _ _ K L f₁ g₂

/-- Associativity for precisely three flat degree-zero source sheaves.
Source: Stacks 0FPL (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def ShiftedTensorAssociativityClause (a b c : ℤ) : Prop :=
  ∀ (P Q S : ShiftedModuleCategory R),
    IsFlatOnSite P → IsFlatOnSite Q → IsFlatOnSite S →
    ∀ (K L M : ShiftedDerivedCategory R)
      (f : shiftedDegreeZero R P ⟶ K⟦a⟧)
      (g : shiftedDegreeZero R Q ⟶ L⟦b⟧)
      (h : shiftedDegreeZero R S ⟶ M⟦c⟧),
      (derivedTensorAssociator R T).hom.app
          ((shiftedDegreeZero R P, shiftedDegreeZero R Q), shiftedDegreeZero R S) ≫
        shiftedTensorB R T a (b + c) _ _ K (T.tensor.obj (L, M)) f
          (shiftedTensorB R T b c _ _ L M g h) =
      shiftedTensorB R T (a + b) c _ _ (T.tensor.obj (K, L)) M
          (shiftedTensorB R T a b _ _ K L f g) h ≫
        (CategoryTheory.shiftFunctor _ ((a + b) + c)).map
          ((derivedTensorAssociator R T).hom.app ((K, L), M)) ≫
        (eqToIso (congrArg
          (fun n : ℤ ↦ (T.tensor.obj (K, T.tensor.obj (L, M)))⟦n⟧)
          (add_assoc a b c))).hom

/-- Symmetry with the scalar (-1)^(ab) and the specified sum-of-shifts identification.
Source: Stacks 0FPM (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def ShiftedTensorSymmetryClause (a b : ℤ) : Prop :=
  ∀ (P Q : ShiftedModuleCategory R), IsFlatOnSite P → IsFlatOnSite Q →
    ∀ (K L : ShiftedDerivedCategory R)
      (f : shiftedDegreeZero R P ⟶ K⟦a⟧)
      (g : shiftedDegreeZero R Q ⟶ L⟦b⟧),
      shiftedTensorB R T a b _ _ K L f g ≫
        (CategoryTheory.shiftFunctor _ (a + b)).map
          ((derivedTensorSymmetry R T).hom.app (K, L)) =
      ((-1 : ℤ) ^ Int.natAbs (a * b)) •
        ((derivedTensorSymmetry R T).hom.app (shiftedDegreeZero R P, shiftedDegreeZero R Q) ≫
          shiftedTensorB R T b a _ _ L K g f ≫
          (eqToIso (congrArg (fun n : ℤ ↦ (T.tensor.obj (L, K))⟦n⟧)
            (add_comm b a))).hom)

/-- The local signed calculus for flat sources and arbitrary derived targets.
Source: Stacks 0FPL/0FPM; all ten proof steps of the DAG node are retained below
(blueprint: lem-pur-shifted-tensor-morphism-calculus).
Proof plan:
1. On E[a]^p tensor F[b]^q, move the second shift first. Its sign is (-1)^(bp);
   the two differential coefficients agree as checked in the node's Step 1.
2. The unsigned associator respects the coefficients 1, (-1)^p, (-1)^(p+q).
   Tensor and shifts preserve K-flatness and flat terms, by tensoring an acyclic
   test complex twice and using flatness of sums and tensor products.
3. Descend these maps and the Koszul swap uniquely using
   lem-weil-pbc-site-derived-tensor-descent, variable by variable.
4. Ordinary additive tensor preserves biproduct diagrams; resolving comparisons
   descend this property. Bilinear composition proves both additivity equations.
5. Associativity signs are bp+c(p+q)=cq+(b+c)p. Descend and precompose with f,g,h.
6. Symmetry signs differ by 2bp: bp+(p+a)(q+b) and ab+pq+aq. Descend and use naturality.
7. Flat degree-zero sheaves are K-flat (lem-pc-kflat-closure). Their tensor is flat
   because tensoring by it is the composite of two exact tensor functors. Thus the
   iterated B operations have the specified flat degree-zero sources.
8. For pullback, use the algebraic inverse image and scalar extension in
   def-weil-pbc-algebraic-inverse-image and the pure-tensor normalization of
   def-weil-pbc-canonical-ringed-tensor-comparison. Its associator and swap squares
   agree on locally generating pure tensors.
9. Module pullback preserves sums by lem-weil-pbc-ringed-topoi-module-adjunction.
   Sum the ordinary comparisons over bidegrees. Additivity preserves all differential,
   shift and swap signs; the unsigned associator is preserved by Step 8.
10. lem-weil-pbc-ringed-topoi-derived-tensor-pullback preserves resolving models.
   Its unique representative comparison descends the Step 9 diagrams. Exactness
   identifies its derived functor with termwise pullback. The degree-zero comparison
   identifies pulled-back f,g with maps out of uStar P,uStar Q, which are flat.
   Naturality of t gives the pullback clause, including all coherence squares. -/
theorem shiftedTensorMorphismCalculus_local (a b c : ℤ) :
    ShiftedTensorAdditivityClause R T a b ∧
    ShiftedTensorAssociativityClause R T a b c ∧
    ShiftedTensorSymmetryClause R T a b := by
  sorry

section Pullback

open CanonicalTensorPullbackOfUniverses
open scoped ChangeOfRings

variable {C' : Type u} [Category.{v} C'] {J' : GrothendieckTopology C'}
  [J'.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasSheafify J' AddCommGrpCat.{max u v}]
  (S RI : Sheaf J' CommRingCat.{max u v})
  [HasDerivedCategory.{w} (ShiftedModuleCategory S)]
  (TS : ShiftedTensorModel S)
  (uInv : Sheaf J (Type (max u v)) ⥤ Sheaf J' (Type (max u v)))
  (uPush : Sheaf J' (Type (max u v)) ⥤ Sheaf J (Type (max u v)))
  (adj : uInv ⊣ uPush) [hlex : PreservesFiniteLimits uInv]
  (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
  (uStar : ShiftedModuleCategory R ⥤ ShiftedModuleCategory S)
  (hobj : ∀ M : ShiftedModuleCategory R, uStar.obj M = changeOfRings c (I.modules.obj M))
  (hmap : ∀ {M N : ShiftedModuleCategory R} (f : M ⟶ N),
    uStar.map f = eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M)
      (I.modules.map f) ≫ eqToHom (hobj N).symm)
  [uStar.Additive] [PreservesFiniteLimits uStar] [PreservesFiniteColimits uStar]
  (V : ShiftedModuleCategory S ⥤ ShiftedModuleCategory R) (am : uStar ⊣ V)
  (k : CanonicalTensorPullbackOfUniverses.CanonicalRingedTensorComparison.{u, v}
    R S RI uInv I c uStar hobj)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types true in
include uPush adj hmap hlex in
/-- The exact pullback comparison is uniquely fixed by the total-complex comparison.
No arbitrary natural isomorphism is assumed. The square uses the canonical ordinary
pure-tensor comparison k and the actual termwise derived functor.
Source: Stacks 07A4/03EL (blueprint: lem-pur-shifted-tensor-morphism-calculus).
Proof (Steps 8--10): use the specified scalar-extension functor and its module adjunction.
The ordinary pure-tensor comparison gives k.totalIso. Exactness makes termwise pullback
invert every quasi-isomorphism. The normalized representative square in
ringedTopoiCanonicalDerivedTensorPullback then gives this comparison; tensor descent
proves uniqueness and independence of representatives. -/
theorem shiftedExactTensorPullback_exists :
    ∃! μ : T.tensor ⋙ uStar.mapDerivedCategory ≅
      (uStar.mapDerivedCategory.prod uStar.mapDerivedCategory) ⋙ TS.tensor,
      ∀ (E F : CochainComplex (ShiftedModuleCategory R) ℤ)
        (hE : shiftedTensorResolving R E) (hF : shiftedTensorResolving R F),
        ∃ (hE' : shiftedTensorResolving S
            ((uStar.mapHomologicalComplex (.up ℤ)).obj E))
          (hF' : shiftedTensorResolving S
            ((uStar.mapHomologicalComplex (.up ℤ)).obj F)),
          uStar.mapDerivedCategory.map
              (T.representative.hom.app (⟨E, hE⟩, ⟨F, hF⟩)) ≫
            μ.hom.app (DerivedCategory.Q.obj E, DerivedCategory.Q.obj F) ≫
            TS.tensor.map (Prod.mkHom (uStar.mapDerivedCategoryFactors.hom.app E)
              (uStar.mapDerivedCategoryFactors.hom.app F)) =
          uStar.mapDerivedCategoryFactors.hom.app ((shiftedTotalTensor R).obj (E, F)) ≫
            DerivedCategory.Q.map (k.totalIso R S RI uInv I c uStar hobj V am E F).inv ≫
            TS.representative.hom.app (⟨_, hE'⟩, ⟨_, hF'⟩) := by
  let LF := uStar.mapDerivedCategory
  let ε := uStar.mapDerivedCategoryFactorsh.hom
  have hLF : LF.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (ShiftedModuleCategory R) (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ LF uStar.mapDerivedCategoryFactorsh
  have hc (E : CochainComplex (ShiftedModuleCategory R) ℤ) :
      derivedPullbackComplexComparison uStar LF ε E =
        uStar.mapDerivedCategoryFactors.hom.app E := exactDerivedComparison uStar E
  have h := CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback
    uInv uPush adj I c uStar
    hobj hmap LF ε hLF (shiftedTensorResolving R) (shiftedTensorResolving S)
    (fun _ ↦ Iff.rfl) (fun _ ↦ Iff.rfl) T.tensor TS.tensor
    T.representative TS.representative k V am
  have hh := h.2
  simp only [hc, Functor.mapIso_inv, LF] at hh
  convert hh using 1
  rfl

/-- The canonical exact derived tensor comparison, fixed by its representative square.
Source: Stacks 07A4 (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def shiftedExactTensorPullback :
    T.tensor ⋙ uStar.mapDerivedCategory ≅
      (uStar.mapDerivedCategory.prod uStar.mapDerivedCategory) ⋙ TS.tensor :=
  (shiftedExactTensorPullback_exists R T S RI TS uInv uPush adj I c uStar
    hobj hmap V am k).exists.choose

/-- All associator, Koszul symmetry and two-shift squares for exact pullback.
The proposition contains equations, rather than an unconstrained coherence hypothesis.
Source: Stacks 03EL/07A4 (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def ShiftedPullbackCoherence
    (μ : T.tensor ⋙ uStar.mapDerivedCategory ≅
      (uStar.mapDerivedCategory.prod uStar.mapDerivedCategory) ⋙ TS.tensor) : Prop :=
  GenericTensorPullbackCoherence T.tensor TS.tensor uStar.mapDerivedCategory
    (shiftedTensorCanonicalComparison R T) (shiftedTensorCanonicalComparison S TS)
    (derivedTensorAssociator R T) (derivedTensorSymmetry R T)
    (derivedTensorAssociator S TS) (derivedTensorSymmetry S TS) μ

/-- The complete ringed-topos clause: flatness preservation, all coherence diagrams,
 and B on the actual pulled-back flat degree-zero source sheaves.
Source: Stacks 03EL, 07A4, 0G7E, 0FPL/0FPM
(blueprint: lem-pur-shifted-tensor-morphism-calculus).
Proof: follow Steps 8--10 of the ten-step plan. Pure tensors
prove ordinary coherence, direct sums give the total-complex comparisons, and additivity
preserves every sign. The normalized derived tensor comparison descends the diagrams
by tensor descent. The preservation clause gives flatness of uStar P (apply it to P[0]).
Exactness gives the termwise derived functor used here. Naturality of the shift square
with respect to f and g proves the B equation; mapDerivedCategorySingleFunctor supplies
exactly the source identification with (uStar P)[0], including identity pullbacks. -/
def ShiftedTensorPullbackClause (a b : ℤ) : Prop :=
    (∀ P : ShiftedModuleCategory R, IsFlatOnSite P → IsFlatOnSite (uStar.obj P)) ∧
    ShiftedPullbackCoherence R T S TS uStar
      (shiftedExactTensorPullback R T S RI TS uInv uPush adj I c uStar hobj hmap V am k) ∧
    ∀ (P Q : ShiftedModuleCategory R), IsFlatOnSite P → IsFlatOnSite Q →
      ∀ (K L : ShiftedDerivedCategory R)
        (f : shiftedDegreeZero R P ⟶ K⟦a⟧)
        (g : shiftedDegreeZero R Q ⟶ L⟦b⟧),
        uStar.mapDerivedCategory.map (shiftedTensorB R T a b _ _ K L f g) ≫
          (uStar.mapDerivedCategory.commShiftIso (a + b)).hom.app (T.tensor.obj (K, L)) ≫
          (CategoryTheory.shiftFunctor _ (a + b)).map
            ((shiftedExactTensorPullback R T S RI TS uInv uPush adj I c uStar
              hobj hmap V am k).hom.app (K, L)) =
        (shiftedExactTensorPullback R T S RI TS uInv uPush adj I c uStar hobj hmap V am k).hom.app
            (shiftedDegreeZero R P, shiftedDegreeZero R Q) ≫
          TS.tensor.map (Prod.mkHom ((uStar.mapDerivedCategorySingleFunctor 0).hom.app P)
            ((uStar.mapDerivedCategorySingleFunctor 0).hom.app Q)) ≫
          shiftedTensorB S TS a b _ _ (uStar.mapDerivedCategory.obj K)
            (uStar.mapDerivedCategory.obj L)
            ((uStar.mapDerivedCategorySingleFunctor 0).inv.app P ≫
              uStar.mapDerivedCategory.map f ≫
              (uStar.mapDerivedCategory.commShiftIso a).hom.app K)
            ((uStar.mapDerivedCategorySingleFunctor 0).inv.app Q ≫
              uStar.mapDerivedCategory.map g ≫
              (uStar.mapDerivedCategory.commShiftIso b).hom.app L)

/-- The full signed calculus and its exact ringed-topos pullback law.
Source: Stacks 0FPL/0FPM; all ten proof steps of the DAG node are retained below
(blueprint: lem-pur-shifted-tensor-morphism-calculus).
Proof plan:
1. On E[a]^p tensor F[b]^q, move the second shift first. Its sign is (-1)^(bp);
   the two differential coefficients agree as checked in the node's Step 1.
2. The unsigned associator respects the coefficients 1, (-1)^p, (-1)^(p+q).
   Tensor and shifts preserve K-flatness and flat terms, by tensoring an acyclic
   test complex twice and using flatness of sums and tensor products.
3. Descend these maps and the Koszul swap uniquely using
   lem-weil-pbc-site-derived-tensor-descent, variable by variable.
4. Ordinary additive tensor preserves biproduct diagrams; resolving comparisons
   descend this property. Bilinear composition proves both additivity equations.
5. Associativity signs are bp+c(p+q)=cq+(b+c)p. Descend and precompose with f,g,h.
6. Symmetry signs differ by 2bp: bp+(p+a)(q+b) and ab+pq+aq. Descend and use naturality.
7. Flat degree-zero sheaves are K-flat (lem-pc-kflat-closure). Their tensor is flat
   because tensoring by it is the composite of two exact tensor functors. Thus the
   iterated B operations have the specified flat degree-zero sources.
8. For pullback, use the algebraic inverse image and scalar extension in
   def-weil-pbc-algebraic-inverse-image and the pure-tensor normalization of
   def-weil-pbc-canonical-ringed-tensor-comparison. Its associator and swap squares
   agree on locally generating pure tensors.
9. Module pullback preserves sums by lem-weil-pbc-ringed-topoi-module-adjunction.
   Sum the ordinary comparisons over bidegrees. Additivity preserves all differential,
   shift and swap signs; the unsigned associator is preserved by Step 8.
10. lem-weil-pbc-ringed-topoi-derived-tensor-pullback preserves resolving models.
   Its unique representative comparison descends the Step 9 diagrams. Exactness
   identifies its derived functor with termwise pullback. The degree-zero comparison
   identifies pulled-back f,g with maps out of uStar P,uStar Q, which are flat.
   Naturality of t gives the pullback clause, including all coherence squares. -/
theorem shiftedTensorMorphismCalculus (a b cshift : ℤ) :
    ShiftedTensorAdditivityClause R T a b ∧
    ShiftedTensorAssociativityClause R T a b cshift ∧
    ShiftedTensorSymmetryClause R T a b ∧
    ShiftedTensorPullbackClause R T S RI TS uInv uPush adj I c uStar hobj hmap V am k a b := by
  sorry

end Pullback
end SheafOfModules
