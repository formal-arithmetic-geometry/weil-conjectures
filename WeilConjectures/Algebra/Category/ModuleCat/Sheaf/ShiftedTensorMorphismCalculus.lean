/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.AlgebraicGeometry.Picard.SiteDerivedTensorDescentIndependentCoefficients
public import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Products.Associator
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorComparisonOfUniverses
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all WeilConjectures.Algebra.Homology.DerivedTensorConstraints.DerivedTensorAdditiveConstraints
import all WeilConjectures.Algebra.Homology.SmoothPurity.TotalTensorSignedCoherence
import WeilConjectures.SecSmoothPurity.CochainPullbackTensorShift
import WeilConjectures.AlgebraicGeometry.Picard.KFlatRingedToposPullback
import WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquationsSupplement

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

end NormalizationPredicates

/-- A tensor functor with its natural resolving comparison. -/
structure ResolvingTensorModel
    {A : Type u₁} [Category.{v₁} A] {D : Type u₂} [Category.{v₂} D]
    (q : A ⥤ D) (P : ObjectProperty A) (t : A × A ⥤ A) where
  tensor : D × D ⥤ D
  representative : (P.ι.prod P.ι) ⋙ t ⋙ q ≅
    ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ tensor

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

end ComplexFormulaPredicates

section
variable {A : Type u₁} [Category.{v₁} A] [Preadditive A]
  [HasZeroObject A] [MonoidalCategory A] [MonoidalPreadditive A]
  [∀ E F : GradedObject ℤ A, GradedObject.HasTensor E F]
  [∀ E F G : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor E F G]
  [∀ E F G : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ E F G]

end



section SignedCoherenceProofs
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
universe uC vC uD vD r
open CategoryTheory.CochainPullback hiding Modules
open SheafOfModules.KFlatFixedTensor
attribute [local irreducible] SheafOfModules.monoidalCategory
  CategoryTheory.Functor.mapHomologicalComplex
  CategoryTheory.Functor.mapBifunctorHomologicalComplex HomologicalComplex₂.total
attribute [local implicit_reducible] HomologicalComplex.monoidalCategoryStruct
  HomologicalComplex.monoidalCategory
  CategoryTheory.Monoidal.induced
attribute [local instance 2000] tensorAdditive tensorObjAdditive tensorHasMapBifunctor
attribute [local irreducible] CategoryTheory.CommShift₂Setup.int
  CategoryTheory.Functor.instCommShiftCochainComplexIntObjMap₂CochainComplex
  CategoryTheory.Functor.instCommShiftCochainComplexIntObjFlipMap₂CochainComplex
set_option maxHeartbeats 800000 in
-- Keep the independent coefficient universes explicit in the comparison interface.
end SignedCoherenceProofs

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
/-- A presentation of the derived tensor by the natural resolving comparison.
This is precisely the tensor and its representative isomorphism from site-derived-tensor
 descent; quantifying over presentations makes the statement independent of this choice.
Source: Stacks 06YU (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
abbrev ShiftedTensorModel :=
  ResolvingTensorModel DerivedCategory.Q (shiftedTensorResolving R) (shiftedTotalTensor R)

@[irreducible]
def shiftedTensorComplexComparisonNatIso (a b : ℤ) :
    ((shiftFunctor (CochainComplex (ShiftedModuleCategory R) ℤ) a).prod
      (shiftFunctor _ b)) ⋙ shiftedTotalTensor R ≅
    shiftedTotalTensor R ⋙ shiftFunctor _ (a + b) :=
  totalTensorPairShift (shiftedOrdinaryTensor R) a b

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

attribute [local irreducible] derivedTensorAssociator

section SignedMorphismProofs
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
attribute [local instance 4001] shiftedOrdinaryTensor_additive
  shiftedOrdinaryTensor_objAdditive shiftedOrdinaryTensor_totalExists
attribute [local instance 4001] DerivedTensorConstraints.complexMonoidal
  DerivedTensorConstraints.complexMonoidalStruct CochainComplex.Monoidal.braidedCategory

attribute [local implicit_reducible] shiftedOrdinaryTensor shiftedTotalTensor
  CategoryTheory.prod.associator

attribute [local semireducible] TensorShiftNormalization TensorSymmetryNormalization
  TensorAssociatorNormalization GenericTensorPullbackCoherence
  siteDerivedTensorIndependentCoefficients shiftedTensorCanonicalComparison
  derivedTensorSymmetry derivedTensorAssociator
set_option maxHeartbeats 800000 in
-- The iterated tensor representatives need additional elaboration heartbeats.
end SignedMorphismProofs

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
section PullbackMorphismProofs
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
attribute [local instance 4001] shiftedOrdinaryTensor_additive
  shiftedOrdinaryTensor_objAdditive shiftedOrdinaryTensor_totalExists
attribute [local instance 4001] DerivedTensorConstraints.complexMonoidal
  DerivedTensorConstraints.complexMonoidalStruct CochainComplex.Monoidal.braidedCategory

attribute [local implicit_reducible] shiftedOrdinaryTensor shiftedTotalTensor
  CategoryTheory.prod.associator

attribute [local semireducible] TensorShiftNormalization TensorSymmetryNormalization
  TensorAssociatorNormalization GenericTensorPullbackCoherence
  siteDerivedTensorIndependentCoefficients shiftedTensorCanonicalComparison
  derivedTensorSymmetry derivedTensorAssociator
section ComplexPullbackProofs
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local implicit_reducible] HomologicalComplex.monoidalCategoryStruct
  HomologicalComplex.monoidalCategory CategoryTheory.Monoidal.induced
attribute [local instance 2000] KFlatFixedTensor.tensorAdditive
  KFlatFixedTensor.tensorObjAdditive KFlatFixedTensor.tensorHasMapBifunctor
attribute [local irreducible] CategoryTheory.CommShift₂Setup.int
  CategoryTheory.Functor.instCommShiftCochainComplexIntObjMap₂CochainComplex
  CategoryTheory.Functor.instCommShiftCochainComplexIntObjFlipMap₂CochainComplex
include uPush adj hmap hlex in
set_option maxHeartbeats 800000 in
-- Compare the two presentations of the canonical total tensor comparison.
include uPush adj hmap hlex in
end ComplexPullbackProofs

set_option maxHeartbeats 1600000 in
-- Paste the representative comparison squares before cancellation.
set_option maxHeartbeats 1600000 in
-- Paste the representative comparison squares before cancellation.
set_option maxHeartbeats 1600000 in
-- Paste the representative comparison squares before cancellation.
end PullbackMorphismProofs

end Pullback
end SheafOfModules
