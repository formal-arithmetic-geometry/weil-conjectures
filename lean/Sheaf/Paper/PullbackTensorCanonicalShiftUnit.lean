/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
public import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Sheaf.SecSmoothPurity.CochainComparisonMonoidalEquations
import Sheaf.Algebra.Homology.KFlatTotalTensorModel
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
import Sheaf.Paper.PullbackTensorResolvingComputation
import Sheaf.Paper.CochainPullbackTensorShift
import Sheaf.Paper.ResolvingRepresentativeWhiskering
import Sheaf.Paper.TensorPullbackRepresentativeDescent
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.ObjectProperty.Shift
import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift

/-! # Canonical shifts and action units of derived tensor pullback

Source: Stacks Project, sites-cohomology.tex, Tags 06YY and 07A4;
more-algebra.tex, Tag 0FNH, item-shift-tensor; sites-modules.tex, Tag 03EL.
(blueprint: lem-weil-pbc-pullback-tensor-canonical-shift-unit).

The helper predicates spell out the normalizations in this node. All tensors,
representative comparisons, cochain unitors and pullback maps are existing ones.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

-- Keep the signed-shift data folded when checking the resolving comparison squares.
attribute [local irreducible] CategoryTheory.CommShift₂Setup.int
attribute [local irreducible]
  CategoryTheory.Functor.instCommShiftCochainComplexIntObjMap₂CochainComplex
  CategoryTheory.Functor.instCommShiftCochainComplexIntObjFlipMap₂CochainComplex

universe uC vC uD vD r wR wS

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits MonoidalCategory
open CategoryTheory.CochainPullback hiding Modules
open SheafOfModules.KFlatFixedTensor

namespace SheafOfModules.PullbackTensorCanonical

@[no_expose] private def fixedRight
    {A B : Type*} [Category A] [Category B]
    (T : A ⥤ A ⥤ A) (T' : B ⥤ B ⥤ B) (G : A ⥤ B)
    (t : Functor.uncurry.obj T ⋙ G ⟶ (G.prod G) ⋙ Functor.uncurry.obj T') (N : A) :
    T.flip.obj N ⋙ G ⟶ G ⋙ T'.flip.obj (G.obj N) where
  app M := t.app (M, N)
  naturality {M M'} a := by
    have h := t.naturality (Prod.mkHom a (𝟙 N))
    change G.map ((T.map a).app N ≫ (T.obj M').map (𝟙 N)) ≫ t.app (M', N) =
      t.app (M, N) ≫ ((T'.map (G.map a)).app (G.obj N) ≫
        (T'.obj (G.obj M')).map (G.map (𝟙 N))) at h
    erw [(T.obj M').map_id N, Category.comp_id, G.map_id N,
      (T'.obj (G.obj M')).map_id (G.obj N), Category.comp_id] at h
    exact h

@[no_expose] private def fixedLeft
    {A B : Type*} [Category A] [Category B]
    (T : A ⥤ A ⥤ A) (T' : B ⥤ B ⥤ B) (G : A ⥤ B)
    (t : Functor.uncurry.obj T ⋙ G ⟶ (G.prod G) ⋙ Functor.uncurry.obj T') (M : A) :
    T.obj M ⋙ G ⟶ G ⋙ T'.obj (G.obj M) where
  app N := t.app (M, N)
  naturality {N N'} b := by
    have h := t.naturality (Prod.mkHom (𝟙 M) b)
    change G.map ((T.map (𝟙 M)).app N ≫ (T.obj M).map b) ≫ t.app (M, N') =
      t.app (M, N) ≫ ((T'.map (G.map (𝟙 M))).app (G.obj N) ≫
        (T'.obj (G.obj M)).map (G.map b)) at h
    erw [T.map_id M, NatTrans.id_app, Category.id_comp, G.map_id M,
      T'.map_id (G.obj M), NatTrans.id_app] at h
    exact h.trans (congrArg (fun z ↦ t.app (M, N) ≫ z)
      (Category.id_comp ((T'.obj (G.obj M)).map (G.map b))))


private theorem fixedRight_shift_equation
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    [HasShift A ℤ] [HasShift B ℤ]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [∀ n : ℤ, (shiftFunctor B n).Additive]
    (T : A ⥤ A ⥤ A) (T' : B ⥤ B ⥤ B) (G : A ⥤ B)
    [T.CommShift₂Int] [T'.CommShift₂Int] [G.CommShift ℤ]
    (t : Functor.uncurry.obj T ⋙ G ⟶ (G.prod G) ⋙ Functor.uncurry.obj T')
    (N : A) [NatTrans.CommShift (fixedRight T T' G t N) ℤ] (n : ℤ) (M : A) :
    t.app (M⟦n⟧, N) ≫ (T'.map ((G.commShiftIso n).hom.app M)).app (G.obj N) ≫
        ((T'.flip.obj (G.obj N)).commShiftIso n).hom.app (G.obj M) =
      G.map (((T.flip.obj N).commShiftIso n).hom.app M) ≫
        (G.commShiftIso n).hom.app ((T.obj M).obj N) ≫ (t.app (M, N))⟦n⟧' := by
  simpa only [Functor.commShiftIso_comp_hom_app, fixedRight,
    Functor.flip_obj_map, Functor.flip_obj_obj, Category.assoc]
    using (NatTrans.shift_app_comm (fixedRight T T' G t N) n M).symm

private theorem fixedLeft_shift_equation
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    [HasShift A ℤ] [HasShift B ℤ]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [∀ n : ℤ, (shiftFunctor B n).Additive]
    (T : A ⥤ A ⥤ A) (T' : B ⥤ B ⥤ B) (G : A ⥤ B)
    [T.CommShift₂Int] [T'.CommShift₂Int] [G.CommShift ℤ]
    (t : Functor.uncurry.obj T ⋙ G ⟶ (G.prod G) ⋙ Functor.uncurry.obj T')
    (M : A) [NatTrans.CommShift (fixedLeft T T' G t M) ℤ] (n : ℤ) (N : A) :
    t.app (M, N⟦n⟧) ≫ (T'.obj (G.obj M)).map ((G.commShiftIso n).hom.app N) ≫
        ((T'.obj (G.obj M)).commShiftIso n).hom.app (G.obj N) =
      G.map (((T.obj M).commShiftIso n).hom.app N) ≫
        (G.commShiftIso n).hom.app ((T.obj M).obj N) ≫ (t.app (M, N))⟦n⟧' := by
  simpa only [Functor.commShiftIso_comp_hom_app, fixedLeft, Category.assoc]
    using (NatTrans.shift_app_comm (fixedLeft T T' G t M) n N).symm

private theorem whiskering_fullyFaithful_iso
    {A B D : Type*} [Category A] [Category B] [Category D]
    (p q : A ⥤ B) (e : p ≅ q)
    (h : Nonempty (((Functor.whiskeringLeft A B D).obj p).FullyFaithful)) :
    Nonempty (((Functor.whiskeringLeft A B D).obj q).FullyFaithful) := by
  obtain ⟨ff⟩ := h
  exact ⟨ff.ofIso ((Functor.whiskeringLeft A B D).mapIso e)⟩

private theorem normalized_square_ext
    {K D E : Type*} [Category K] [Category D] [Category E]
    (q : K ⥤ D) (P : ObjectProperty K)
    (ff : ((Functor.whiskeringLeft (P.FullSubcategory × P.FullSubcategory)
      (D × D) E).obj ((P.ι ⋙ q).prod (P.ι ⋙ q))).FullyFaithful)
    {F G : D × D ⥤ E} (a b : F ⟶ G) (U V : K → K → E)
    (r : ∀ (X Y : K) (_ : P X) (_ : P Y), U X Y ≅ F.obj (q.obj X, q.obj Y))
    (e : ∀ (X Y : K) (_ : P X) (_ : P Y), G.obj (q.obj X, q.obj Y) ⟶ V X Y)
    (he : ∀ X Y hx hy, IsIso (e X Y hx hy))
    (h : ∀ X Y hx hy, (r X Y hx hy).hom ≫ a.app (q.obj X, q.obj Y) ≫ e X Y hx hy =
      (r X Y hx hy).hom ≫ b.app (q.obj X, q.obj Y) ≫ e X Y hx hy) : a = b := by
  apply ff.map_injective
  apply NatTrans.ext
  funext Z
  obtain ⟨⟨X, hx⟩, ⟨Y, hy⟩⟩ := Z
  change a.app (q.obj X, q.obj Y) = b.app (q.obj X, q.obj Y)
  have := he X Y hx hy
  apply (cancel_epi (r X Y hx hy).hom).1
  apply (cancel_mono (e X Y hx hy)).1
  simpa only [Category.assoc] using h X Y hx hy

@[no_expose] private def uncurry_comparison
    {A B : Type*} [Category A] [Category B]
    (T : A ⥤ A ⥤ A) (T' : B ⥤ B ⥤ B) (F : A ⥤ B)
    (t : (Functor.postcompose₂.obj F).obj T ⟶
      (((Functor.whiskeringLeft₂ B).obj F).obj F).obj T')
    (h : ∀ P Q, IsIso ((t.app P).app Q)) :
    Functor.uncurry.obj T ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj T' :=
  NatIso.ofComponents (fun X ↦ @asIso _ _ _ _ ((t.app X.1).app X.2) (h X.1 X.2)) (by
    intro X Y a
    have ha := NatTrans.congr_app (t.naturality a.1) X.2
    have hb := (t.app Y.1).naturality a.2
    change F.map ((T.map a.1).app X.2) ≫ (t.app Y.1).app X.2 =
      (t.app X.1).app X.2 ≫ (T'.map (F.map a.1)).app (F.obj X.2) at ha
    change F.map ((T.obj Y.1).map a.2) ≫ (t.app Y.1).app Y.2 =
      (t.app Y.1).app X.2 ≫ (T'.obj (F.obj Y.1)).map (F.map a.2) at hb
    change F.map ((T.map a.1).app X.2 ≫ (T.obj Y.1).map a.2) ≫
      (t.app Y.1).app Y.2 = (t.app X.1).app X.2 ≫
      ((T'.map (F.map a.1)).app (F.obj X.2) ≫ (T'.obj (F.obj Y.1)).map (F.map a.2))
    rw [F.map_comp, Category.assoc, hb, ← Category.assoc, ha, Category.assoc])

private theorem uncurry_comparison_hom_app
    {A B : Type*} [Category A] [Category B]
    (T : A ⥤ A ⥤ A) (T' : B ⥤ B ⥤ B) (F : A ⥤ B)
    (t : (Functor.postcompose₂.obj F).obj T ⟶
      (((Functor.whiskeringLeft₂ B).obj F).obj F).obj T')
    (h : ∀ P Q, IsIso ((t.app P).app Q)) (X : A × A) :
    (uncurry_comparison T T' F t h).hom.app X = (t.app X.1).app X.2 := rfl

attribute [local irreducible] uncurry_comparison

private theorem tensor_right_unit_naturality
    {B : Type*} [Category B] (T : B ⥤ B ⥤ B) (U : B)
    (rho : T.flip.obj U ⟶ 𝟭 B)
    {X X' Y Y' : B} (a : X ⟶ X') (b : Y ⟶ Y') (j : Y' ⟶ U) :
    (T.obj X).map (b ≫ j) ≫ rho.app X ≫ a =
      (Functor.uncurry.obj T).map (Prod.mkHom a b) ≫
        (T.obj X').map j ≫ rho.app X' := by
  have h := rho.naturality a
  change (T.map a).app U ≫ rho.app X' = rho.app X ≫ a at h
  rw [Functor.map_comp, Category.assoc, ← h]
  rw [← Category.assoc ((T.obj X).map j), NatTrans.naturality]
  simp only [Functor.uncurry_obj_map, Category.assoc]
  rw [NatTrans.naturality_assoc]

private theorem tensor_left_unit_naturality
    {B : Type*} [Category B] (T : B ⥤ B ⥤ B) (U : B)
    (ell : T.obj U ⟶ 𝟭 B)
    {X X' Y Y' : B} (a : X ⟶ X') (b : Y ⟶ Y') (j : X' ⟶ U) :
    (T.map (a ≫ j)).app Y ≫ ell.app Y ≫ b =
      (Functor.uncurry.obj T).map (Prod.mkHom a b) ≫
        (T.map j).app Y' ≫ ell.app Y' := by
  have h := ell.naturality b
  change (T.obj U).map b ≫ ell.app Y' = ell.app Y ≫ b at h
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [← h, ← NatTrans.naturality_assoc]
  simp only [Functor.uncurry_obj_map, Category.assoc]

private theorem normalized_right_unit_diagram
    {D E : Type*} [Category D] [Category E] (L : D ⥤ E)
    (T : E ⥤ E ⥤ E) (U : E) (rho : T.flip.obj U ⟶ 𝟭 E)
    {X Y Z V : D} {A B C H : E}
    (s : Z ⟶ V) [IsIso s] (r : V ⟶ X) (p : Z ⟶ X)
    (t : L.obj V ⟶ (T.obj (L.obj X)).obj (L.obj Y))
    (a : L.obj X ⟶ A) [Mono a] (b : L.obj Y ⟶ B) (j : B ⟶ U)
    (e : L.obj Z ⟶ C) (c : C ⟶ H) (q : H ⟶ (T.obj A).obj B) (v : H ⟶ A)
    (hs : s ≫ r = p)
    (hn : L.map s ≫ t ≫ (Functor.uncurry.obj T).map (Prod.mkHom a b) = e ≫ c ≫ q)
    (hu : q ≫ (T.obj A).map j ≫ rho.app A = v)
    (hc : e ≫ c ≫ v = L.map p ≫ a) :
    t ≫ (T.obj (L.obj X)).map (b ≫ j) ≫ rho.app (L.obj X) = L.map r := by
  apply (cancel_epi (L.map s)).1
  apply (cancel_mono a).1
  simp only [Category.assoc]
  rw [tensor_right_unit_naturality T U rho a b j]
  rw [reassoc_of% hn, hu, hc]
  rw [← Category.assoc, ← L.map_comp, hs]

private theorem normalized_left_unit_diagram
    {D E : Type*} [Category D] [Category E] (L : D ⥤ E)
    (T : E ⥤ E ⥤ E) (U : E) (ell : T.obj U ⟶ 𝟭 E)
    {X Y Z V : D} {A B C H : E}
    (s : Z ⟶ V) [IsIso s] (r : V ⟶ Y) (p : Z ⟶ Y)
    (t : L.obj V ⟶ (T.obj (L.obj X)).obj (L.obj Y))
    (a : L.obj X ⟶ A) (b : L.obj Y ⟶ B) [Mono b] (j : A ⟶ U)
    (e : L.obj Z ⟶ C) (c : C ⟶ H) (q : H ⟶ (T.obj A).obj B) (v : H ⟶ B)
    (hs : s ≫ r = p)
    (hn : L.map s ≫ t ≫ (Functor.uncurry.obj T).map (Prod.mkHom a b) = e ≫ c ≫ q)
    (hu : q ≫ (T.map j).app B ≫ ell.app B = v)
    (hc : e ≫ c ≫ v = L.map p ≫ b) :
    t ≫ (T.map (a ≫ j)).app (L.obj Y) ≫ ell.app (L.obj Y) = L.map r := by
  apply (cancel_epi (L.map s)).1
  apply (cancel_mono b).1
  simp only [Category.assoc]
  rw [tensor_left_unit_naturality T U ell a b j]
  rw [reassoc_of% hn, hu, hc]
  rw [← Category.assoc, ← L.map_comp, hs]

private theorem fixed_shift_transport
    {A B C D E : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (i : A ⥤ B) (Q : B ⥤ D) (Q' : C ⥤ E) (F : B ⥤ C) (L : D ⥤ E)
    (T₀ : B ⥤ B) (T₁ : D ⥤ D) (T₂ T₄ : E ⥤ E) (T₃ : C ⥤ C)
    [i.CommShift ℤ] [Q.CommShift ℤ] [Q'.CommShift ℤ] [F.CommShift ℤ]
    [L.CommShift ℤ] [T₀.CommShift ℤ] [T₁.CommShift ℤ] [T₂.CommShift ℤ]
    [T₃.CommShift ℤ] [T₄.CommShift ℤ]
    (epsilon : Q ⋙ L ⟶ F ⋙ Q') [NatTrans.CommShift epsilon ℤ]
    (he : ∀ A, IsIso (epsilon.app (i.obj A)))
    (cR : T₀ ⋙ Q ≅ Q ⋙ T₁) [NatTrans.CommShift cR.hom ℤ]
    (cS : T₃ ⋙ Q' ≅ Q' ⋙ T₄) [NatTrans.CommShift cS.hom ℤ]
    (chi : T₀ ⋙ F ⟶ F ⋙ T₃) [NatTrans.CommShift chi ℤ]
    (beta : T₂ ≅ T₄) [NatTrans.CommShift beta.hom ℤ]
    (t : T₁ ⋙ L ⟶ L ⋙ T₂)
    (hn : ∀ A, L.map (cR.hom.app (i.obj A)) ≫ t.app (Q.obj (i.obj A)) ≫
      T₂.map (epsilon.app (i.obj A)) ≫ beta.hom.app (Q'.obj (F.obj (i.obj A))) =
      epsilon.app (T₀.obj (i.obj A)) ≫ Q'.map (chi.app (i.obj A)) ≫
        cS.hom.app (F.obj (i.obj A))) :
    NatTrans.CommShift (Functor.whiskerLeft (i ⋙ Q) t) ℤ := by
  let q := i ⋙ Q
  let ee' : i ⋙ (Q ⋙ L) ≅ i ⋙ (F ⋙ Q') :=
    NatIso.ofComponents (fun A ↦ @asIso _ _ _ _ (epsilon.app (i.obj A)) (he A))
      (fun a ↦ epsilon.naturality (i.map a))
  have : NatTrans.CommShift ee'.hom ℤ := by
    change NatTrans.CommShift (Functor.whiskerLeft i epsilon) ℤ
    infer_instance
  let ee : q ⋙ L ≅ (i ⋙ F) ⋙ Q' :=
    Functor.associator i Q L ≪≫ ee' ≪≫ (Functor.associator i F Q').symm
  have : NatTrans.CommShift ee.hom ℤ := by dsimp [ee]; infer_instance
  let e₁ := isoWhiskerRight (Functor.associator i T₀ Q) L ≪≫
    isoWhiskerRight (isoWhiskerLeft i cR) L ≪≫
    isoWhiskerRight (Functor.associator i Q T₁).symm L ≪≫
    Functor.associator q T₁ L
  let e₂ : q ⋙ (L ⋙ T₂) ≅ ((i ⋙ F) ⋙ Q') ⋙ T₄ :=
    (Functor.associator q L T₂).symm ≪≫ isoWhiskerRight ee T₂ ≪≫
      isoWhiskerLeft ((i ⋙ F) ⋙ Q') beta
  have : NatTrans.CommShift e₁.hom ℤ := by dsimp [e₁]; infer_instance
  have : NatTrans.CommShift e₂.hom ℤ := by dsimp [e₂]; infer_instance
  let w := (Functor.associator (i ⋙ T₀) Q L).hom ≫
    Functor.whiskerLeft (i ⋙ T₀) epsilon ≫
    (Functor.associator (i ⋙ T₀) F Q').inv ≫
    (isoWhiskerRight (Functor.associator i T₀ F) Q').hom ≫
    Functor.whiskerRight (Functor.whiskerLeft i chi) Q' ≫
    (isoWhiskerRight (Functor.associator i F T₃).symm Q').hom ≫
    (Functor.associator (i ⋙ F) T₃ Q').hom ≫
    (isoWhiskerLeft (i ⋙ F) cS).hom ≫
    (Functor.associator (i ⋙ F) Q' T₄).inv
  have : NatTrans.CommShift w ℤ := by dsimp [w]; infer_instance
  have hh : e₁.hom ≫ Functor.whiskerLeft q t ≫ e₂.hom = w := by
    apply NatTrans.ext
    funext A
    have hee : ee'.hom.app A = epsilon.app (i.obj A) := rfl
    simpa [e₁, e₂, w, ee, q, hee, Category.assoc] using hn A
  have ht : Functor.whiskerLeft q t = e₁.inv ≫ w ≫ e₂.inv := by
    rw [← hh]
    simp
  rw [ht]
  infer_instance

private theorem fixed_shift_transport_models
    {A B C D E : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (i : A ⥤ B) (Q : B ⥤ D) (Q' : C ⥤ E) (F : B ⥤ C) (L : D ⥤ E)
    (T₀ : B ⥤ B) (T₁ : D ⥤ D) (T₂ T₄ : E ⥤ E) (T₃ : C ⥤ C)
    [i.CommShift ℤ] [Q.CommShift ℤ] [Q'.CommShift ℤ] [F.CommShift ℤ]
    [L.CommShift ℤ] [T₀.CommShift ℤ] [T₁.CommShift ℤ] [T₂.CommShift ℤ]
    [T₃.CommShift ℤ] [T₄.CommShift ℤ]
    (epsilon : Q ⋙ L ⟶ F ⋙ Q') [NatTrans.CommShift epsilon ℤ]
    (he : ∀ A, IsIso (epsilon.app (i.obj A)))
    (P₁ P₂ : B → Prop) (S₁ S₂ : C → Prop)
    (hi : ∀ A, P₁ (i.obj A) ∧ P₂ (i.obj A))
    (hF : ∀ X, P₁ X → P₂ X → S₁ (F.obj X) ∧ S₂ (F.obj X))
    (r : ∀ (X : B) (_ : P₁ X) (_ : P₂ X), Q.obj (T₀.obj X) ≅ T₁.obj (Q.obj X))
    (s : ∀ (Y : C) (_ : S₁ Y) (_ : S₂ Y), Q'.obj (T₃.obj Y) ≅ T₄.obj (Q'.obj Y))
    (hcR : ∃ cR : T₀ ⋙ Q ≅ Q ⋙ T₁, NatTrans.CommShift cR.hom ℤ ∧
      ∀ X hx₁ hx₂, cR.app X = r X hx₁ hx₂)
    (hcS : ∃ cS : T₃ ⋙ Q' ≅ Q' ⋙ T₄, NatTrans.CommShift cS.hom ℤ ∧
      ∀ Y hy₁ hy₂, cS.app Y = s Y hy₁ hy₂)
    (chi : T₀ ⋙ F ⟶ F ⋙ T₃) [NatTrans.CommShift chi ℤ]
    (beta : T₂ ≅ T₄) [NatTrans.CommShift beta.hom ℤ]
    (t : T₁ ⋙ L ⟶ L ⋙ T₂)
    (hn : ∀ A, L.map (r (i.obj A) (hi A).1 (hi A).2).hom ≫
      t.app (Q.obj (i.obj A)) ≫ T₂.map (epsilon.app (i.obj A)) ≫
        beta.hom.app (Q'.obj (F.obj (i.obj A))) =
      epsilon.app (T₀.obj (i.obj A)) ≫ Q'.map (chi.app (i.obj A)) ≫
        (s (F.obj (i.obj A)) (hF (i.obj A) (hi A).1 (hi A).2).1
          (hF (i.obj A) (hi A).1 (hi A).2).2).hom) :
    NatTrans.CommShift (Functor.whiskerLeft (i ⋙ Q) t) ℤ := by
  obtain ⟨cR, hcr, hr⟩ := hcR
  obtain ⟨cS, hcs, hs⟩ := hcS
  apply fixed_shift_transport i Q Q' F L T₀ T₁ T₂ T₄ T₃ epsilon he cR cS chi beta t
  intro A
  change L.map (cR.app (i.obj A)).hom ≫ _ = _ ≫ _ ≫
    (cS.app (F.obj (i.obj A))).hom
  rw [hr (i.obj A) (hi A).1 (hi A).2,
    hs (F.obj (i.obj A)) (hF (i.obj A) (hi A).1 (hi A).2).1
      (hF (i.obj A) (hi A).1 (hi A).2).2]
  exact hn A

private theorem descend_action_unitor
    {A D : Type*} [Category A] [Category D]
    (W : MorphismProperty A) (Q : A ⥤ D) [Q.IsLocalization W]
    (T₀ : A ⥤ A) (T₁ : D ⥤ D) (c : T₀ ⋙ Q ≅ Q ⋙ T₁) (u : T₀ ≅ 𝟭 A) :
    ∃ rho : T₁ ≅ 𝟭 D, ∀ P, c.hom.app P ≫ rho.hom.app (Q.obj P) = Q.map (u.hom.app P) := by
  let ff := Localization.fullyFaithfulWhiskeringLeft Q W D
  let e : Q ⋙ T₁ ≅ Q ⋙ 𝟭 D := c.symm ≪≫ isoWhiskerRight u Q
  let rho := ff.preimageIso e
  refine ⟨rho, ?_⟩
  intro P
  have h := NatTrans.congr_app (ff.map_preimage e.hom) P
  change rho.hom.app (Q.obj P) = c.inv.app P ≫ Q.map (u.hom.app P) at h
  exact (congrArg (fun z ↦ c.hom.app P ≫ z) h).trans (Iso.hom_inv_id_app_assoc c P _)

private theorem cochain_unit_terms_flat
    {A : Type*} [Category A] [Preadditive A] [MonoidalCategory A]
    [HasZeroObject A] [HasFiniteCoproducts A]
    [(curriedTensor A).Additive] [∀ M, ((curriedTensor A).obj M).Additive]
    [∀ M, PreservesFiniteColimits ((curriedTensor A).obj M)]
    (n : ℤ) : exactFunctor A A
      (tensorRight ((HomologicalComplex.tensorUnit A (.up ℤ)).X n)) := by
  by_cases hn : n = 0
  · subst n
    have hu : exactFunctor A A (tensorRight (𝟙_ A)) :=
      ⟨preservesFiniteLimits_of_natIso (rightUnitorNatIso A).symm,
        preservesFiniteColimits_of_natIso (rightUnitorNatIso A).symm⟩
    exact (exactFunctor _ _).prop_of_iso
      ((curriedTensor A).flip.mapIso
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ A)).symm) hu
  · let T := tensorRight ((HomologicalComplex.tensorUnit A (.up ℤ)).X n)
    have hz : IsZero T := T.isZero (fun M ↦
      (tensorLeft M).map_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (𝟙_ A) n hn))
    let := T.preservesLimitsOfSize_of_isZero hz
    let := T.preservesColimitsOfSize_of_isZero hz
    change PreservesFiniteLimits T ∧ PreservesFiniteColimits T
    exact ⟨inferInstance, inferInstance⟩


-- Use the smaller limit-preservation instance while elaborating this file.
attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan

attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local irreducible] siteDerivedTensorIndependentCoefficients
attribute [local irreducible] representativeIso
attribute [local irreducible] DerivedCategory.Q DerivedCategory.Qh
attribute [local irreducible] Functor.curry
attribute [local irreducible] Functor.mapHomologicalComplex
attribute [local irreducible] Functor.mapBifunctorHomologicalComplex
attribute [local irreducible] HomologicalComplex₂.total
attribute [local irreducible] CategoryTheory.CochainPullback.comparison
attribute [local irreducible] CategoryTheory.CochainPullback.unit
attribute [local irreducible] HomologicalComplex.single
attribute [local irreducible] HomologicalComplex.rightUnitor HomologicalComplex.leftUnitor

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{r} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {R : Sheaf J CommRingCat.{r}} {S : Sheaf K CommRingCat.{r}}
  [HasDerivedCategory.{wR} (Modules.{uC, vC, r} R)]
  [HasDerivedCategory.{wS} (Modules.{uD, vD, r} S)]

local notation "MR" => Modules (C := C) (J := J) R
local notation "MS" => Modules (C := D) (J := K) S
variable (R) in
/-- The published derived tensor with a stable name for its presentation.
The data is exactly `derivedTensor R`; no localization is reselected.
Source: Stacks 06YU.
(blueprint: lem-weil-pbc-pullback-tensor-canonical-shift-unit). -/
def canonicalDerivedTensor : DerivedCategory (MR) ⥤ DerivedCategory (MR) ⥤
    DerivedCategory (MR) := derivedTensor R

/-- The given published shift structure, in the stable derived-tensor presentation.
This definition returns its input structure; it selects no new comparisons.
Source: Stacks 06YU and 0FNH.
(blueprint: lem-weil-pbc-pullback-tensor-canonical-shift-unit). -/
@[instance_reducible]
def canonicalDerivedTensorCommShift [(derivedTensor R).CommShift₂Int] :
    (canonicalDerivedTensor R).CommShift₂Int :=
  inferInstanceAs (derivedTensor R).CommShift₂Int

attribute [local instance] canonicalDerivedTensorCommShift

local notation "TR" => canonicalDerivedTensor (C := C) (J := J) R
local notation "TS" => canonicalDerivedTensor (C := D) (J := K) S
local notation "tR₀" => totalTensor (C := C) (J := J) R
local notation "tS₀" => totalTensor (C := D) (J := K) S
local notation "DR" => derivedTensor (C := C) (J := J) R
local notation "DS" => derivedTensor (C := D) (J := K) S

variable (R) in
/-- The published resolving isomorphism in the stable derived-tensor presentation.
Source: Stacks 06YU.
(blueprint: lem-weil-pbc-pullback-tensor-canonical-shift-unit). -/
def canonicalRepresentativeIso
    (P Q : CochainComplex (MR) ℤ) (hp : P.IsKFlatIndependentCoefficients)
    (hq : Q.IsKFlatIndependentCoefficients)
    (hf : ∀ n, IsFlatOnSite (J := J) (R := R) (P.X n))
    (hg : ∀ n, IsFlatOnSite (J := J) (R := R) (Q.X n)) :
    DerivedCategory.Q.obj (((tR₀).obj P).obj Q) ≅
      ((TR).obj (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj Q) :=
  representativeIso R P Q hp hq hf hg

/-- Normalization of the two derived tensor shifts by signed total-complex shifts.
The fixed-argument comparisons agree with the published resolving comparison.
`CommShift` includes the zero and addition laws, and `CommShift₂Int` includes
naturality in the other derived argument.
Source: Stacks 06YU and 0FNH
(blueprint: lem-weil-pbc-pullback-tensor-canonical-shift-unit). -/
def HasCanonicalTensorShifts [(DR).CommShift₂Int] : Prop :=
  ∀ (P : CochainComplex (MR) ℤ) (hp : P.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)),
    (∃ cL : (tR₀).obj P ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ (TR).obj (DerivedCategory.Q.obj P),
      NatTrans.CommShift cL.hom ℤ ∧
      ∀ (Q : CochainComplex (MR) ℤ) (hq : Q.IsKFlatIndependentCoefficients)
        (hg : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (Q.X n)),
        cL.app Q = canonicalRepresentativeIso.{uC, vC, r, wR} R P Q hp hq hf hg) ∧
    (∃ cR : (tR₀).flip.obj P ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ (TR).flip.obj (DerivedCategory.Q.obj P),
      NatTrans.CommShift cR.hom ℤ ∧
      ∀ (Q : CochainComplex (MR) ℤ) (hq : Q.IsKFlatIndependentCoefficients)
        (hg : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (Q.X n)),
        cR.app Q = canonicalRepresentativeIso.{uC, vC, r, wR} R Q P hq hp hg hf)

set_option genSizeOf false in
set_option genCtorIdx false in
set_option genInjectivity false in
/-- The action unitors, specified on flat-term K-flat representatives by the
ordinary cochain action maps. The ring complex is itself a resolving complex.
Source: Stacks 06YU and 03EL
(blueprint: lem-weil-pbc-pullback-tensor-canonical-shift-unit). -/
structure ActionUnits where
  unit_kflat : CochainComplex.IsKFlatIndependentCoefficients
    (HomologicalComplex.tensorUnit (MR) (.up ℤ))
  unit_flat : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R)
    ((HomologicalComplex.tensorUnit (MR) (.up ℤ)).X n)
  rho : (TR).flip.obj
    (DerivedCategory.Q.obj (HomologicalComplex.tensorUnit (MR) (.up ℤ))) ≅
      𝟭 (DerivedCategory (MR))
  ell : (TR).obj
    (DerivedCategory.Q.obj (HomologicalComplex.tensorUnit (MR) (.up ℤ))) ≅
      𝟭 (DerivedCategory (MR))
  rho_normalized : ∀ (P : CochainComplex (MR) ℤ) (hp : P.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)),
    (canonicalRepresentativeIso.{uC, vC, r, wR} R P (HomologicalComplex.tensorUnit (MR) (.up ℤ))
      hp unit_kflat hf unit_flat).hom ≫
      rho.hom.app (DerivedCategory.Q.obj P) = DerivedCategory.Q.map
        (HomologicalComplex.rightUnitor P).hom
  ell_normalized : ∀ (P : CochainComplex (MR) ℤ) (hp : P.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)),
    (canonicalRepresentativeIso.{uC, vC, r, wR} R (HomologicalComplex.tensorUnit (MR) (.up ℤ)) P
      unit_kflat hp unit_flat hf).hom ≫
      ell.hom.app (DerivedCategory.Q.obj P) =
        DerivedCategory.Q.map (HomologicalComplex.leftUnitor P).hom

variable (f : RingedPullback.{r, uC, vC, uD, vD} R S)
  (k : Comparison.{r, uC, vC, uD, vD} (J := J) (K := K) (R := R) (S := S) f)
  (L : DerivedCategory (Modules.{uC, vC, r} R) ⥤
    DerivedCategory (Modules.{uD, vD, r} S))

variable (epsilon : DerivedCategory.Q ⋙ L ⟶
  pull.{r, uC, vC, uD, vD} (J := J) (K := K) (R := R) (S := S) f ⋙ DerivedCategory.Q)

local notation "pullF" => pull (J := J) (K := K) (R := R) (S := S) f

/-- The two derived bifunctors in the comparison.
Source: Stacks 07A4
(blueprint: lem-weil-pbc-pullback-tensor-canonical-shift-unit). -/
abbrev Phi := Functor.uncurry.obj (TR) ⋙ L

/-- Pull back each input before taking the published derived tensor.
Source: Stacks 07A4
(blueprint: lem-weil-pbc-pullback-tensor-canonical-shift-unit). -/
abbrev Psi := (L.prod L) ⋙ Functor.uncurry.obj (TS)

/-- The Tag 07A4 representative square, in an equivalent form avoiding inverses
of computation maps. Its cochain comparison is the prescribed insertion-of-one map.
Source: Stacks 07A4
(blueprint: lem-weil-pbc-pullback-tensor-canonical-shift-unit). -/
def IsNormalized (tau : Phi L ⟶ Psi L) : Prop :=
  ∀ (P Q : CochainComplex (MR) ℤ) (hp : P.IsKFlatIndependentCoefficients)
    (hq : Q.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n))
    (hg : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (Q.X n)),
    ∃ (hp' : CochainComplex.IsKFlatIndependentCoefficients
        ((pullF).obj P))
      (hq' : CochainComplex.IsKFlatIndependentCoefficients
        ((pullF).obj Q))
      (hf' : ∀ n : ℤ, IsFlatOnSite (J := K) (R := S) (((pullF).obj P).X n))
      (hg' : ∀ n : ℤ, IsFlatOnSite (J := K) (R := S) (((pullF).obj Q).X n)),
      L.map (canonicalRepresentativeIso.{uC, vC, r, wR} R P Q hp hq hf hg).hom ≫
          tau.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
          (Functor.uncurry.obj (TS)).map
            (Prod.mkHom (epsilon.app P) (epsilon.app Q)) =
        epsilon.app (((tR₀).obj P).obj Q) ≫
          DerivedCategory.Q.map (comparison.{r, uC, vC, uD, vD}
            (J := J) (K := K) (R := R) (S := S) f k P Q).hom ≫
          (canonicalRepresentativeIso.{uD, vD, r, wS} S
            ((pullF).obj P) ((pullF).obj Q)
            hp' hq' hf' hg').hom



set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem canonicalTensorShifts_exists :
    ∃ s : (DR).CommShift₂Int,
      letI := s; HasCanonicalTensorShifts (R := R) := by
  obtain ⟨s, hs⟩ := kFlat_fixed_tensor_triangulated.{uC, vC, r, wR} R
  refine ⟨s, ?_⟩
  intro P hp hf
  exact ⟨(hs P hp hf).2.2.2.1, (hs P hp hf).2.2.2.2.1⟩

attribute [local irreducible] canonicalDerivedTensor canonicalRepresentativeIso

omit [HasDerivedCategory.{wR} (Modules.{uC, vC, r} R)] in
private theorem unit_resolving :
    CochainComplex.IsKFlatIndependentCoefficients
      (J := J) (R := R) (HomologicalComplex.tensorUnit (MR) (.up ℤ)) ∧
      ∀ n, IsFlatOnSite (J := J) (R := R)
        ((HomologicalComplex.tensorUnit (MR) (.up ℤ)).X n) := by
  let := SheafOfModules.monoidalCategory R
  refine ⟨?_, ?_⟩
  · intro F hF
    exact fun i ↦ (hF i).of_iso (HomologicalComplex.rightUnitor F).symm
  · intro n
    apply (exactFunctor _ _).prop_of_iso
      (siteSheafTensorRightIso R
        ((HomologicalComplex.tensorUnit (MR) (.up ℤ)).X n)).symm
    exact cochain_unit_terms_flat n

private lemma square_comp
    {A : Type*} [Category A] {X₀ X₁ X₂ Y₀ Y₁ Y₂ : A}
    {a : X₀ ⟶ X₁} {b : X₁ ⟶ X₂} {c : Y₀ ⟶ Y₁} {d : Y₁ ⟶ Y₂}
    {r₀ : X₀ ⟶ Y₀} {r₁ : X₁ ⟶ Y₁} {r₂ : X₂ ⟶ Y₂}
    (ha : a ≫ r₁ = r₀ ≫ c) (hb : b ≫ r₂ = r₁ ≫ d) :
    (a ≫ b) ≫ r₂ = r₀ ≫ (c ≫ d) := by
  rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc]

private lemma representative_naturality
    [(DR).CommShift₂Int] (hc :
      HasCanonicalTensorShifts (R := R))
    (P Q P' Q' : CochainComplex (Modules.{uC, vC, r} (C := C) (J := J) R) ℤ)
    (hp : P.IsKFlatIndependentCoefficients) (hq : Q.IsKFlatIndependentCoefficients)
    (hp' : P'.IsKFlatIndependentCoefficients) (hq' : Q'.IsKFlatIndependentCoefficients)
    (hf : ∀ n, IsFlatOnSite (J := J) (R := R) (P.X n))
    (hg : ∀ n, IsFlatOnSite (J := J) (R := R) (Q.X n))
    (hf' : ∀ n, IsFlatOnSite (J := J) (R := R) (P'.X n))
    (hg' : ∀ n, IsFlatOnSite (J := J) (R := R) (Q'.X n))
    (a : P ⟶ P') (b : Q ⟶ Q') :
    DerivedCategory.Q.map
        (((totalTensor.{uC, vC, r} (C := C) (J := J) R).map a).app Q ≫ ((totalTensor.{uC, vC, r}
          (C := C) (J := J) R).obj P').map b) ≫
        (canonicalRepresentativeIso.{uC, vC, r, wR} R P' Q' hp' hq' hf' hg').hom =
      (canonicalRepresentativeIso.{uC, vC, r, wR} R P Q hp hq hf hg).hom ≫
        (((TR).map (DerivedCategory.Q.map a)).app
          (DerivedCategory.Q.obj Q) ≫
          ((TR).obj (DerivedCategory.Q.obj P')).map
            (DerivedCategory.Q.map b)) := by
  obtain ⟨c₁, _, h₁⟩ := (hc Q hq hg).2
  obtain ⟨c₂, _, h₂⟩ := (hc P' hp' hf').1
  have ha := c₁.hom.naturality a
  have hb := c₂.hom.naturality b
  change DerivedCategory.Q.map (((totalTensor.{uC, vC, r} (C := C) (J := J) R).map a).app Q) ≫
    c₁.hom.app P' =
    c₁.hom.app P ≫ (((TR).map
      (DerivedCategory.Q.map a)).app
      (DerivedCategory.Q.obj Q)) at ha
  change DerivedCategory.Q.map (((totalTensor.{uC, vC, r} (C := C) (J := J) R).obj P').map b) ≫
    c₂.hom.app Q' =
    c₂.hom.app Q ≫ ((TR).obj (DerivedCategory.Q.obj
      P')).map
      (DerivedCategory.Q.map b) at hb
  change _ ≫ (c₁.app P').hom = (c₁.app P).hom ≫ _ at ha
  change _ ≫ (c₂.app Q').hom = (c₂.app Q).hom ≫ _ at hb
  rw [h₁ P hp hf, h₁ P' hp' hf'] at ha
  rw [h₂ Q hq hg, h₂ Q' hq' hg'] at hb
  exact (congrArg (fun z ↦ z ≫
    (canonicalRepresentativeIso.{uC, vC, r, wR} R P' Q' hp' hq' hf' hg').hom)
      (DerivedCategory.Q.map_comp
        (((totalTensor.{uC, vC, r} R).map a).app Q)
        (((totalTensor.{uC, vC, r} R).obj P').map b))).trans (square_comp ha hb)


omit [HasDerivedCategory.{wR} (Modules.{uC, vC, r} R)] in
@[no_expose] private abbrev resolvingProperty : ObjectProperty (CochainComplex (MR) ℤ) :=
  fun P ↦ P.IsKFlatIndependentCoefficients ∧
    ∀ n, IsFlatOnSite (J := J) (R := R) (P.X n)

@[no_expose] private noncomputable def resolvingTensorIso
    [(DR).CommShift₂Int] (hc : HasCanonicalTensorShifts (R := R)) :
    ((resolvingProperty (R := R)).ι.prod (resolvingProperty (R := R)).ι) ⋙
        Functor.uncurry.obj (tR₀) ⋙ DerivedCategory.Q ≅
      (((resolvingProperty (R := R)).ι ⋙ DerivedCategory.Q).prod
        ((resolvingProperty (R := R)).ι ⋙ DerivedCategory.Q)) ⋙
          Functor.uncurry.obj (TR) :=
  NatIso.ofComponents
    (fun X ↦ canonicalRepresentativeIso.{uC, vC, r, wR} R X.1.obj X.2.obj
      X.1.property.1 X.2.property.1 X.1.property.2 X.2.property.2)
    (fun {X Y} a ↦ representative_naturality (R := R) hc X.1.obj X.2.obj Y.1.obj Y.2.obj
      X.1.property.1 X.2.property.1 Y.1.property.1 Y.2.property.1
      X.1.property.2 X.2.property.2 Y.1.property.2 Y.2.property.2 a.1.hom a.2.hom)

private theorem resolvingTensorIso_hom_app
    [(DR).CommShift₂Int] (hc : HasCanonicalTensorShifts (R := R))
    (X : (resolvingProperty (R := R)).FullSubcategory ×
      (resolvingProperty (R := R)).FullSubcategory) :
    (resolvingTensorIso (R := R) hc).hom.app X =
      (canonicalRepresentativeIso.{uC, vC, r, wR} R X.1.obj X.2.obj
        X.1.property.1 X.2.property.1 X.1.property.2 X.2.property.2).hom := rfl

attribute [local irreducible] resolvingTensorIso

omit [HasDerivedCategory.{wR} (Modules.{uC, vC, r} R)] in
private theorem exists_resolving
    (A : CochainComplex (MR) ℤ) :
    ∃ (P : CochainComplex (MR) ℤ) (a : P ⟶ A), resolvingProperty (R := R) P ∧
      QuasiIso a := by
  obtain ⟨P, a, hp, hf, ha, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients A
  have hflat : ∀ n, IsFlatOnSite (J := J) (R := R) (P.X n) := fun n ↦
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (P.X n)).symm (hf n)
  exact ⟨P, a, ⟨hp, hflat⟩, ha⟩

private theorem derivedNatTrans_ext
    {F G : DerivedCategory (MR) ⥤ DerivedCategory (MS)}
    (a b : F ⟶ G)
    (h : ∀ (P : CochainComplex (MR) ℤ) (_hp : P.IsKFlatIndependentCoefficients)
      (_hf : ∀ n, IsFlatOnSite (J := J) (R := R) (P.X n)),
      a.app (DerivedCategory.Q.obj P) = b.app (DerivedCategory.Q.obj P)) : a = b := by
  apply NatTrans.ext
  funext M
  let A := DerivedCategory.Q.objPreimage M
  obtain ⟨P, r, ⟨hp, hflat⟩, hr⟩ := exists_resolving (R := R) A
  have := hr
  let e := asIso (DerivedCategory.Q.map r) ≪≫ DerivedCategory.Q.objObjPreimageIso M
  apply (cancel_epi (F.map e.hom)).1
  rw [a.naturality, b.naturality, h P hp hflat]

private theorem resolving_essSurj :
    ((resolvingProperty (R := R)).ι ⋙ DerivedCategory.Q).EssSurj := by
  constructor
  intro M
  let A := DerivedCategory.Q.objPreimage M
  obtain ⟨P, a, ⟨hp, hflat⟩, ha⟩ := exists_resolving (R := R) A
  have := ha
  exact ⟨⟨P, hp, hflat⟩, ⟨asIso (DerivedCategory.Q.map a) ≪≫
    DerivedCategory.Q.objObjPreimageIso M⟩⟩

private theorem resolving_shift : (resolvingProperty (R := R)).IsStableUnderShift ℤ := by
  obtain ⟨s, hs⟩ := kFlat_fixed_tensor_triangulated.{uC, vC, r, wR} R
  exact ⟨fun n ↦ ⟨fun P hp ↦ (hs P hp.1 hp.2).2.1 n⟩⟩

private theorem actionUnits_subsingleton : Subsingleton (ActionUnits (R := R)) := by
  refine ⟨fun a b ↦ ?_⟩
  have hr : a.rho = b.rho := by
    apply Iso.ext
    apply derivedNatTrans_ext (R := R) (S := R)
    intro P hp hf
    apply (cancel_epi (canonicalRepresentativeIso.{uC, vC, r, wR} R P
      (HomologicalComplex.tensorUnit (MR) (.up ℤ))
      hp a.unit_kflat hf a.unit_flat).hom).1
    exact (a.rho_normalized P hp hf).trans (b.rho_normalized P hp hf).symm
  have hl : a.ell = b.ell := by
    apply Iso.ext
    apply derivedNatTrans_ext (R := R) (S := R)
    intro P hp hf
    apply (cancel_epi (canonicalRepresentativeIso.{uC, vC, r, wR} R
      (HomologicalComplex.tensorUnit (MR) (.up ℤ)) P
      a.unit_kflat hp a.unit_flat hf).hom).1
    exact (a.ell_normalized P hp hf).trans (b.ell_normalized P hp hf).symm
  cases a
  cases b
  cases hr
  cases hl
  rfl

private theorem actionUnits_exists [(DR).CommShift₂Int]
    (hc : HasCanonicalTensorShifts (R := R)) : Nonempty (ActionUnits (R := R)) := by
  let := SheafOfModules.monoidalCategory R
  let U := HomologicalComplex.tensorUnit (MR) (.up ℤ)
  obtain ⟨hk, hf⟩ := unit_resolving (R := R)
  obtain ⟨cL, _, hcL⟩ := (hc U hk hf).1
  obtain ⟨cR, _, hcR⟩ := (hc U hk hf).2
  obtain ⟨rho, hrho⟩ := descend_action_unitor
    (HomologicalComplex.quasiIso (MR) (.up ℤ)) DerivedCategory.Q
    ((tR₀).flip.obj U) ((TR).flip.obj (DerivedCategory.Q.obj U)) cR
    (rightUnitorNatIso (CochainComplex (MR) ℤ))
  obtain ⟨ell, hell⟩ := descend_action_unitor
    (HomologicalComplex.quasiIso (MR) (.up ℤ)) DerivedCategory.Q
    ((tR₀).obj U) ((TR).obj (DerivedCategory.Q.obj U)) cL
    (leftUnitorNatIso (CochainComplex (MR) ℤ))
  refine ⟨⟨hk, hf, rho, ell, ?_, ?_⟩⟩
  · intro P hp hflat
    exact (congrArg (fun e : _ ≅ _ ↦ e.hom ≫ rho.hom.app (DerivedCategory.Q.obj P))
      (hcR P hp hflat).symm).trans (hrho P)
  · intro P hp hflat
    exact (congrArg (fun e : _ ≅ _ ↦ e.hom ≫ ell.hom.app (DerivedCategory.Q.obj P))
      (hcL P hp hflat).symm).trans (hell P)



private theorem resolving_fullyFaithful :
    let P := resolvingProperty (R := R)
    Nonempty (((Functor.whiskeringLeft (P.FullSubcategory × P.FullSubcategory)
      (DerivedCategory (MR) × DerivedCategory (MR)) (DerivedCategory (MS))).obj
        ((P.ι ⋙ DerivedCategory.Q).prod (P.ι ⋙ DerivedCategory.Q))).FullyFaithful) := by
  let PR := resolvingProperty (R := R)
  let PH : ObjectProperty (HomotopyCategory (MR) (.up ℤ)) := fun X ↦ PR X.as
  have hres : ∀ X : HomotopyCategory (MR) (.up ℤ),
      ∃ (Y : PH.FullSubcategory) (a : Y.obj ⟶ X),
        HomotopyCategory.quasiIso (MR) (.up ℤ) a := by
    intro X
    obtain ⟨P, a, ⟨hp, hflat⟩, ha⟩ := exists_resolving (R := R) X.as
    exact ⟨⟨(HomotopyCategory.quotient _ (.up ℤ)).obj P, hp, hflat⟩,
      (HomotopyCategory.quotient _ (.up ℤ)).map a,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff a).2 ha⟩
  have hff := CategoryTheory.resolvingRepresentativesFullyFaithfulWhiskering
    (K := CochainComplex (MR) ℤ) (H := HomotopyCategory (MR) (.up ℤ))
    (D := DerivedCategory (MR)) (DerivedCategory (MS))
    (HomotopyCategory.quotient _ (.up ℤ)) HomotopyCategory.quotient_obj_surjective
    (HomotopyCategory.quasiIso (MR) (.up ℤ)) DerivedCategory.Qh
    PR PH (fun _ ↦ Iff.rfl) hres
  exact whiskering_fullyFaithful_iso _ _
    (NatIso.prod (isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso (MR)))
      (isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso (MR)))) hff

private theorem normalized_comparison
    [(DR).CommShift₂Int] [(DS).CommShift₂Int]
    (hcR : HasCanonicalTensorShifts (R := R)) (hcS : HasCanonicalTensorShifts (R := S))
    (hL : L.IsLeftDerivedFunctor epsilon
      (HomologicalComplex.quasiIso (MR) (.up ℤ))) :
    ∃ mu : Phi L ≅ Psi L, IsNormalized f k L epsilon mu.hom ∧
      ∀ tau : Phi L ⟶ Psi L, IsNormalized f k L epsilon tau → tau = mu.hom := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  let : J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r}) := inferInstance
  let : K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r}) := inferInstance
  let := f.finiteLimits
  let PR := resolvingProperty (R := R)
  let PS := resolvingProperty (R := S)
  have hF : ∀ P, PR P → PS ((pullF).obj P) := by
    intro P hp
    exact isKFlat_ringedToposPullback f.uInv f.uPush f.adj f.I f.coefficient f.L
      f.hobj f.hmap P hp.1 hp.2
  have he : ∀ P, PR P → IsIso (epsilon.app P) := by
    intro P hp
    exact PullbackTensorResolving.pullback_resolving_computation f L epsilon hL P hp.1 hp.2
  obtain ⟨ff'⟩ := resolving_fullyFaithful (R := R) (S := S)
  let tR := Functor.uncurry.obj (tR₀)
  let tS := Functor.uncurry.obj (tS₀)
  let b : tR ⋙ pullF ≅ ((pullF).prod (pullF)) ⋙ tS :=
    uncurry_comparison (tR₀) (tS₀) (pullF) (tensorComparisonNatTrans f k)
      (fun P Q ↦ show IsIso (comparison f k P Q).hom from inferInstance)
  have het : ∀ P Q, PR P → PR Q → IsIso (epsilon.app (tR.obj (P, Q))) := by
    intro P Q hp hq
    have ht := KFlatTotalTensorModel.kFlat_total_tensor_model R P Q hp.1 hq.1 hp.2 hq.2
    exact he _ ⟨ht.1, ht.2.1⟩
  obtain ⟨mu, hmu, _⟩ := CategoryTheory.tensorComparisonDescent
    DerivedCategory.Q DerivedCategory.Q (pullF) L epsilon
    PR PS hF ff' tR tS (Functor.uncurry.obj (TR))
    (Functor.uncurry.obj (TS))
    (resolvingTensorIso (R := R) hcR) (resolvingTensorIso (R := S) hcS) b he het
  have hn : IsNormalized f k L epsilon mu.hom := by
    intro P Q hp hq hf hg
    have hh := hmu P Q ⟨hp, hf⟩ ⟨hq, hg⟩
    have hb : b.hom.app (P, Q) = (comparison f k P Q).hom :=
      uncurry_comparison_hom_app (tR₀) (tS₀) (pullF) (tensorComparisonNatTrans f k)
        (fun A B ↦ show IsIso (comparison f k A B).hom from inferInstance) (P, Q)
    rw [hb] at hh
    simp only [resolvingTensorIso_hom_app] at hh
    exact ⟨(hF P ⟨hp, hf⟩).1, (hF Q ⟨hq, hg⟩).1,
      (hF P ⟨hp, hf⟩).2, (hF Q ⟨hq, hg⟩).2, hh⟩
  refine ⟨mu, hn, ?_⟩
  intro tau ht
  apply normalized_square_ext DerivedCategory.Q PR ff' tau mu.hom
    (fun X Y ↦ L.obj (DerivedCategory.Q.obj (((tR₀).obj X).obj Y)))
    (fun X Y ↦ ((TS).obj (DerivedCategory.Q.obj ((pullF).obj X))).obj
      (DerivedCategory.Q.obj ((pullF).obj Y)))
    (fun X Y hx hy ↦ L.mapIso (canonicalRepresentativeIso R X Y hx.1 hy.1 hx.2 hy.2))
    (fun X Y _ _ ↦ (Functor.uncurry.obj (TS)).map
      (Prod.mkHom (epsilon.app X) (epsilon.app Y)))
  · intro X Y hx hy
    have := he X hx
    have := he Y hy
    have : IsIso (Prod.mkHom (epsilon.app X) (epsilon.app Y)) :=
      (isIso_prod_iff (f := Prod.mkHom (epsilon.app X) (epsilon.app Y))).2
        ⟨inferInstance, inferInstance⟩
    infer_instance
  · intro X Y hx hy
    obtain ⟨_, _, _, _, hτ⟩ := ht X Y hx.1 hy.1 hx.2 hy.2
    obtain ⟨_, _, _, _, hμ⟩ := hn X Y hx.1 hy.1 hx.2 hy.2
    exact hτ.trans hμ.symm


@[no_expose] private def fixedRightComparison (mu : Phi L ≅ Psi L)
    (N : DerivedCategory (MR)) :
    (TR).flip.obj N ⋙ L ⟶ L ⋙ (TS).flip.obj (L.obj N) :=
  fixedRight (TR) (TS) L mu.hom N

@[no_expose] private def fixedLeftComparison (mu : Phi L ≅ Psi L)
    (M : DerivedCategory (MR)) :
    (TR).obj M ⋙ L ⟶ L ⋙ (TS).obj (L.obj M) :=
  fixedLeft (TR) (TS) L mu.hom M

set_option maxHeartbeats 1000000 in
-- Comparing the total-tensor and monoidal cochain presentations needs extra heartbeats.
private theorem rightShift_resolving
    [L.CommShift ℤ] [NatTrans.CommShift epsilon ℤ]
    [(DR).CommShift₂Int] [(DS).CommShift₂Int]
    (hcR : HasCanonicalTensorShifts (R := R)) (hcS : HasCanonicalTensorShifts (R := S))
    (mu : Phi L ≅ Psi L) (hm : IsNormalized f k L epsilon mu.hom)
    (hL : L.IsLeftDerivedFunctor epsilon
      (HomologicalComplex.quasiIso (MR) (.up ℤ)))
    (N : CochainComplex (MR) ℤ) (hn : N.IsKFlatIndependentCoefficients)
    (hnf : ∀ n, IsFlatOnSite (J := J) (R := R) (N.X n)) :
    NatTrans.CommShift (fixedRightComparison L mu (DerivedCategory.Q.obj N)) ℤ := by
  let P := resolvingProperty (R := R)
  let := resolving_shift (R := R)
  let := resolving_essSurj (R := R)
  let i := P.ι
  let q := i ⋙ DerivedCategory.Q
  let F := pullF
  have hF : ∀ A, P A → resolvingProperty (R := S) (F.obj A) := by
    intro A ha
    let := f.finiteLimits
    exact isKFlat_ringedToposPullback f.uInv f.uPush f.adj f.I f.coefficient f.L
      f.hobj f.hmap A ha.1 ha.2
  have he : ∀ A, P A → IsIso (epsilon.app A) := fun A ha ↦
    PullbackTensorResolving.pullback_resolving_computation f L epsilon hL A ha.1 ha.2
  have heN := he N ⟨hn, hnf⟩
  let chi : (tR₀).flip.obj N ⋙ F ⟶ F ⋙ (tS₀).flip.obj (F.obj N) :=
    (tensorComparisonNatTrans f k).flipApp N
  have : NatTrans.CommShift chi ℤ := (tensorComparison_commShift f k).2 N
  let beta := (TS).flip.mapIso (asIso (epsilon.app N))
  have : NatTrans.CommShift beta.hom ℤ := by dsimp [beta]; infer_instance
  have hh : NatTrans.CommShift (Functor.whiskerLeft q
      (fixedRightComparison L mu (DerivedCategory.Q.obj N))) ℤ := by
    apply fixed_shift_transport_models i DerivedCategory.Q DerivedCategory.Q F L
      ((tR₀).flip.obj N) ((TR).flip.obj (DerivedCategory.Q.obj N))
      ((TS).flip.obj (L.obj (DerivedCategory.Q.obj N)))
      ((TS).flip.obj (DerivedCategory.Q.obj (F.obj N)))
      ((tS₀).flip.obj (F.obj N)) epsilon (fun A ↦ he A.obj A.property)
      (fun A ↦ CochainComplex.IsKFlatIndependentCoefficients A)
      (fun A ↦ ∀ n, IsFlatOnSite (J := J) (R := R) (A.X n))
      (fun A ↦ CochainComplex.IsKFlatIndependentCoefficients A)
      (fun A ↦ ∀ n, IsFlatOnSite (J := K) (R := S) (A.X n))
      (fun A ↦ A.property) (fun A ha hf ↦ hF A ⟨ha, hf⟩)
      (fun A ha hf ↦ canonicalRepresentativeIso R A N ha hn hf hnf)
      (fun A ha hf ↦ canonicalRepresentativeIso S A (F.obj N) ha (hF N ⟨hn, hnf⟩).1
          hf (hF N ⟨hn, hnf⟩).2)
      ((hcR N hn hnf).2)
      ((hcS (F.obj N) (hF N ⟨hn, hnf⟩).1 (hF N ⟨hn, hnf⟩).2).2)
      chi beta (fixedRightComparison L mu (DerivedCategory.Q.obj N))
    intro A
    obtain ⟨ha, hb, haf, hbf, hh⟩ := hm A.obj N A.property.1 hn A.property.2 hnf
    exact hh
  exact NatTrans.CommShift.of_whiskerLeft _ q
    (fun X ↦ ⟨q.objPreimage X, (q.objObjPreimageIso X).inv, inferInstance⟩)

private theorem rightShift_global
    [L.CommShift ℤ] [NatTrans.CommShift epsilon ℤ]
    [(DR).CommShift₂Int] [(DS).CommShift₂Int]
    (hcR : HasCanonicalTensorShifts (R := R)) (hcS : HasCanonicalTensorShifts (R := S))
    (mu : Phi L ≅ Psi L) (hm : IsNormalized f k L epsilon mu.hom)
    (hL : L.IsLeftDerivedFunctor epsilon
      (HomologicalComplex.quasiIso (MR) (.up ℤ)))
    (N : DerivedCategory (MR)) :
    NatTrans.CommShift (fixedRightComparison L mu N) ℤ := by
  let P := resolvingProperty (R := R)
  let q := P.ι ⋙ DerivedCategory.Q
  let := resolving_essSurj (R := R)
  let A := q.objPreimage N
  let e := q.objObjPreimageIso N
  have := rightShift_resolving f k L epsilon hcR hcS mu hm hL A.obj A.property.1 A.property.2
  let e₁ := isoWhiskerRight ((TR).flip.mapIso e) L
  let e₂ := isoWhiskerLeft L ((TS).flip.mapIso (L.mapIso e))
  have : NatTrans.CommShift e₁.hom ℤ := by dsimp [e₁]; infer_instance
  have : NatTrans.CommShift e₂.hom ℤ := by dsimp [e₂]; infer_instance
  have ht : fixedRightComparison L mu N =
      e₁.inv ≫ fixedRightComparison L mu (q.obj A) ≫ e₂.hom := by
    apply (cancel_epi e₁.hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    apply NatTrans.ext
    funext M
    exact (fixedLeftComparison L mu M).naturality e.hom
  have hh : NatTrans.CommShift (fixedRightComparison L mu (q.obj A)) ℤ := by
    change NatTrans.CommShift (fixedRightComparison L mu (DerivedCategory.Q.obj A.obj)) ℤ
    infer_instance
  rw [ht]
  infer_instance


set_option maxHeartbeats 1000000 in
-- Comparing the total-tensor and monoidal cochain presentations needs extra heartbeats.
private theorem leftShift_resolving
    [L.CommShift ℤ] [NatTrans.CommShift epsilon ℤ]
    [(DR).CommShift₂Int] [(DS).CommShift₂Int]
    (hcR : HasCanonicalTensorShifts (R := R)) (hcS : HasCanonicalTensorShifts (R := S))
    (mu : Phi L ≅ Psi L) (hm : IsNormalized f k L epsilon mu.hom)
    (hL : L.IsLeftDerivedFunctor epsilon
      (HomologicalComplex.quasiIso (MR) (.up ℤ)))
    (N : CochainComplex (MR) ℤ) (hn : N.IsKFlatIndependentCoefficients)
    (hnf : ∀ n, IsFlatOnSite (J := J) (R := R) (N.X n)) :
    NatTrans.CommShift (fixedLeftComparison L mu (DerivedCategory.Q.obj N)) ℤ := by
  let P := resolvingProperty (R := R)
  let := resolving_shift (R := R)
  let := resolving_essSurj (R := R)
  let i := P.ι
  let q := i ⋙ DerivedCategory.Q
  let F := pullF
  have hF : ∀ A, P A → resolvingProperty (R := S) (F.obj A) := by
    intro A ha
    let := f.finiteLimits
    exact isKFlat_ringedToposPullback f.uInv f.uPush f.adj f.I f.coefficient f.L
      f.hobj f.hmap A ha.1 ha.2
  have he : ∀ A, P A → IsIso (epsilon.app A) := fun A ha ↦
    PullbackTensorResolving.pullback_resolving_computation f L epsilon hL A ha.1 ha.2
  have heN := he N ⟨hn, hnf⟩
  let chi : (tR₀).obj N ⋙ F ⟶ F ⋙ (tS₀).obj (F.obj N) :=
    (tensorComparisonNatTrans f k).app N
  have : NatTrans.CommShift chi ℤ := (tensorComparison_commShift f k).1 N
  let beta := (TS).mapIso (asIso (epsilon.app N))
  have : NatTrans.CommShift beta.hom ℤ := by dsimp [beta]; infer_instance
  have hh : NatTrans.CommShift (Functor.whiskerLeft q
      (fixedLeftComparison L mu (DerivedCategory.Q.obj N))) ℤ := by
    apply fixed_shift_transport_models i DerivedCategory.Q DerivedCategory.Q F L
      ((tR₀).obj N) ((TR).obj (DerivedCategory.Q.obj N))
      ((TS).obj (L.obj (DerivedCategory.Q.obj N)))
      ((TS).obj (DerivedCategory.Q.obj (F.obj N)))
      ((tS₀).obj (F.obj N)) epsilon (fun A ↦ he A.obj A.property)
      (fun A ↦ CochainComplex.IsKFlatIndependentCoefficients A)
      (fun A ↦ ∀ n, IsFlatOnSite (J := J) (R := R) (A.X n))
      (fun A ↦ CochainComplex.IsKFlatIndependentCoefficients A)
      (fun A ↦ ∀ n, IsFlatOnSite (J := K) (R := S) (A.X n))
      (fun A ↦ A.property) (fun A ha hf ↦ hF A ⟨ha, hf⟩)
      (fun A ha hf ↦ canonicalRepresentativeIso R N A hn ha hnf hf)
      (fun A ha hf ↦ canonicalRepresentativeIso S (F.obj N) A (hF N ⟨hn, hnf⟩).1 ha
          (hF N ⟨hn, hnf⟩).2 hf)
      ((hcR N hn hnf).1)
      ((hcS (F.obj N) (hF N ⟨hn, hnf⟩).1 (hF N ⟨hn, hnf⟩).2).1)
      chi beta (fixedLeftComparison L mu (DerivedCategory.Q.obj N))
    intro A
    obtain ⟨ha, hb, haf, hbf, hh⟩ := hm N A.obj hn A.property.1 hnf A.property.2
    have hnat := beta.hom.naturality (epsilon.app A.obj)
    change ((TS).obj (L.obj (DerivedCategory.Q.obj N))).map (epsilon.app A.obj) ≫
      beta.hom.app (DerivedCategory.Q.obj (F.obj A.obj)) =
      ((TS).map (epsilon.app N)).app (L.obj (DerivedCategory.Q.obj A.obj)) ≫
        ((TS).obj (DerivedCategory.Q.obj (F.obj N))).map (epsilon.app A.obj) at hnat
    have hnat' := congrArg (fun z ↦
      L.map (canonicalRepresentativeIso R N A.obj hn A.property.1 hnf A.property.2).hom ≫
        mu.hom.app (DerivedCategory.Q.obj N, DerivedCategory.Q.obj A.obj) ≫ z) hnat
    have hh' := hnat'.trans hh
    exact hh'
  exact NatTrans.CommShift.of_whiskerLeft _ q
    (fun X ↦ ⟨q.objPreimage X, (q.objObjPreimageIso X).inv, inferInstance⟩)

private theorem leftShift_global
    [L.CommShift ℤ] [NatTrans.CommShift epsilon ℤ]
    [(DR).CommShift₂Int] [(DS).CommShift₂Int]
    (hcR : HasCanonicalTensorShifts (R := R)) (hcS : HasCanonicalTensorShifts (R := S))
    (mu : Phi L ≅ Psi L) (hm : IsNormalized f k L epsilon mu.hom)
    (hL : L.IsLeftDerivedFunctor epsilon
      (HomologicalComplex.quasiIso (MR) (.up ℤ)))
    (N : DerivedCategory (MR)) :
    NatTrans.CommShift (fixedLeftComparison L mu N) ℤ := by
  let P := resolvingProperty (R := R)
  let q := P.ι ⋙ DerivedCategory.Q
  let := resolving_essSurj (R := R)
  let A := q.objPreimage N
  let e := q.objObjPreimageIso N
  have := leftShift_resolving f k L epsilon hcR hcS mu hm hL A.obj A.property.1 A.property.2
  let e₁ := isoWhiskerRight ((TR).mapIso e) L
  let e₂ := isoWhiskerLeft L ((TS).mapIso (L.mapIso e))
  have : NatTrans.CommShift e₁.hom ℤ := by dsimp [e₁]; infer_instance
  have : NatTrans.CommShift e₂.hom ℤ := by dsimp [e₂]; infer_instance
  have ht : fixedLeftComparison L mu N =
      e₁.inv ≫ fixedLeftComparison L mu (q.obj A) ≫ e₂.hom := by
    apply (cancel_epi e₁.hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    apply NatTrans.ext
    funext M
    exact (fixedRightComparison L mu M).naturality e.hom
  have hh : NatTrans.CommShift (fixedLeftComparison L mu (q.obj A)) ℤ := by
    change NatTrans.CommShift (fixedLeftComparison L mu (DerivedCategory.Q.obj A.obj)) ℤ
    infer_instance
  rw [ht]
  infer_instance


set_option maxHeartbeats 1000000 in
-- Converting the published total tensor to its cochain monoidal presentation is costly.
private theorem rightUnit_representative
    [(DR).CommShift₂Int] [(DS).CommShift₂Int]
    (hcS : HasCanonicalTensorShifts (R := S))
    (aR : ActionUnits (R := R)) (aS : ActionUnits (R := S))
    (mu : Phi L ≅ Psi L) (hm : IsNormalized f k L epsilon mu.hom)
    (P : CochainComplex (MR) ℤ) (hp : P.IsKFlatIndependentCoefficients)
    (hf : ∀ n, IsFlatOnSite (J := J) (R := R) (P.X n))
    (he : IsIso (epsilon.app P)) :
    mu.hom.app (DerivedCategory.Q.obj P,
        DerivedCategory.Q.obj (HomologicalComplex.tensorUnit (MR) (.up ℤ))) ≫
      ((TS).obj (L.obj (DerivedCategory.Q.obj P))).map
        (epsilon.app (HomologicalComplex.tensorUnit (MR) (.up ℤ)) ≫
          DerivedCategory.Q.map (CategoryTheory.CochainPullback.unit
            (R := R) (S := S) f k).hom) ≫
      aS.rho.hom.app (L.obj (DerivedCategory.Q.obj P)) =
        L.map (aR.rho.hom.app (DerivedCategory.Q.obj P)) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  let U := HomologicalComplex.tensorUnit (MR) (.up ℤ)
  let V := HomologicalComplex.tensorUnit (MS) (.up ℤ)
  let F := pullF
  let j : F.obj U ⟶ V :=
    (CategoryTheory.CochainPullback.unit (R := R) (S := S) f k).hom
  let rP : ((tR₀).obj P).obj U ⟶ P := (HomologicalComplex.rightUnitor P).hom
  let rFP : ((tS₀).obj (F.obj P)).obj V ⟶ F.obj P :=
    (HomologicalComplex.rightUnitor (F.obj P)).hom
  let c : F.obj (((tR₀).obj P).obj U) ⟶
      ((tS₀).obj (F.obj P)).obj (F.obj U) := (comparison f k P U).hom
  obtain ⟨hp', hu', hf', huf', hnorm⟩ := hm P U hp aR.unit_kflat hf aR.unit_flat
  change _ = epsilon.app (((tR₀).obj P).obj U) ≫ DerivedCategory.Q.map c ≫
    (canonicalRepresentativeIso S (F.obj P) (F.obj U) hp' hu' hf' huf').hom at hnorm
  obtain ⟨cL, _, hcL⟩ := (hcS (F.obj P) hp' hf').1
  have hn := cL.hom.naturality j
  change DerivedCategory.Q.map (((tS₀).obj (F.obj P)).map j) ≫
    (cL.app V).hom = (cL.app (F.obj U)).hom ≫
      ((TS).obj (DerivedCategory.Q.obj (F.obj P))).map (DerivedCategory.Q.map j) at hn
  erw [hcL V aS.unit_kflat aS.unit_flat, hcL (F.obj U) hu' huf'] at hn
  have hunit :
      (canonicalRepresentativeIso.{uD, vD, r, wS} S (F.obj P) (F.obj U) hp' hu' hf' huf').hom ≫
          ((TS).obj (DerivedCategory.Q.obj (F.obj P))).map
            (DerivedCategory.Q.map j) ≫
          aS.rho.hom.app (DerivedCategory.Q.obj (F.obj P)) =
        DerivedCategory.Q.map
          (((tS₀).obj (F.obj P)).map j ≫
            rFP) := by
    erw [← Category.assoc, ← hn, Category.assoc, aS.rho_normalized,
      ← Functor.map_comp]
  have hchain : F.map rP = c ≫
      ((tS₀).obj (F.obj P)).map j ≫ rFP :=
    (cochainComparison_monoidal.{r, uC, vC, uD, vD} f k).2.2.2.2 P
  have heps := epsilon.naturality rP
  have hcomm : epsilon.app (((tR₀).obj P).obj U) ≫ DerivedCategory.Q.map c ≫
      DerivedCategory.Q.map (((tS₀).obj (F.obj P)).map j ≫ rFP) =
        L.map (DerivedCategory.Q.map rP) ≫ epsilon.app P := by
    rw [← DerivedCategory.Q.map_comp, ← hchain]
    exact heps.symm
  exact normalized_right_unit_diagram L (TS) (DerivedCategory.Q.obj V) aS.rho.hom
    (canonicalRepresentativeIso R P U hp aR.unit_kflat hf aR.unit_flat).hom
    (aR.rho.hom.app (DerivedCategory.Q.obj P)) (DerivedCategory.Q.map rP)
    (mu.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj U))
    (epsilon.app P) (epsilon.app U) (DerivedCategory.Q.map j)
    (epsilon.app (((tR₀).obj P).obj U)) (DerivedCategory.Q.map c)
    (canonicalRepresentativeIso S (F.obj P) (F.obj U) hp' hu' hf' huf').hom
    (DerivedCategory.Q.map (((tS₀).obj (F.obj P)).map j ≫ rFP))
    (aR.rho_normalized P hp hf) hnorm hunit hcomm


private theorem rightUnit_equation
    [(DR).CommShift₂Int] [(DS).CommShift₂Int]
    (hcS : HasCanonicalTensorShifts (R := S))
    (aR : ActionUnits (R := R)) (aS : ActionUnits (R := S))
    (mu : Phi L ≅ Psi L) (hm : IsNormalized f k L epsilon mu.hom)
    (hL : L.IsLeftDerivedFunctor epsilon
      (HomologicalComplex.quasiIso (MR) (.up ℤ)))
    (u : L.obj (DerivedCategory.Q.obj
        (HomologicalComplex.tensorUnit (MR) (.up ℤ))) ≅
      DerivedCategory.Q.obj (HomologicalComplex.tensorUnit (MS) (.up ℤ)))
    (hu : u.hom = epsilon.app (HomologicalComplex.tensorUnit (MR) (.up ℤ)) ≫
      DerivedCategory.Q.map (CategoryTheory.CochainPullback.unit
        (R := R) (S := S) f k).hom) :
    ∀ M, mu.hom.app
        (M, DerivedCategory.Q.obj (HomologicalComplex.tensorUnit (MR) (.up ℤ))) ≫
      ((TS).obj (L.obj M)).map u.hom ≫ aS.rho.hom.app (L.obj M) =
        L.map (aR.rho.hom.app M) := by
  let a := fixedRightComparison L mu
      (DerivedCategory.Q.obj (HomologicalComplex.tensorUnit (MR) (.up ℤ))) ≫
    Functor.whiskerLeft L ((TS).flip.map u.hom) ≫
    Functor.whiskerLeft L aS.rho.hom
  let b := Functor.whiskerRight aR.rho.hom L
  have hab : a = b := by
    apply derivedNatTrans_ext (R := R) (S := S)
    intro P hp hf
    change mu.hom.app _ ≫ _ ≫ _ = _
    rw [hu]
    exact rightUnit_representative f k L epsilon hcS aR aS mu hm P hp hf
      (PullbackTensorResolving.pullback_resolving_computation f L epsilon hL P hp hf)
  exact fun M ↦ NatTrans.congr_app hab M


set_option maxHeartbeats 1000000 in
-- Converting the published total tensor to its cochain monoidal presentation is costly.
private theorem leftUnit_representative
    [(DR).CommShift₂Int] [(DS).CommShift₂Int]
    (hcS : HasCanonicalTensorShifts (R := S))
    (aR : ActionUnits (R := R)) (aS : ActionUnits (R := S))
    (mu : Phi L ≅ Psi L) (hm : IsNormalized f k L epsilon mu.hom)
    (P : CochainComplex (MR) ℤ) (hp : P.IsKFlatIndependentCoefficients)
    (hf : ∀ n, IsFlatOnSite (J := J) (R := R) (P.X n))
    (he : IsIso (epsilon.app P)) :
    mu.hom.app (DerivedCategory.Q.obj (HomologicalComplex.tensorUnit
        (MR) (.up ℤ)), DerivedCategory.Q.obj P) ≫
      ((TS).map
        (epsilon.app (HomologicalComplex.tensorUnit (MR) (.up ℤ)) ≫
          DerivedCategory.Q.map (CategoryTheory.CochainPullback.unit
            (R := R) (S := S) f k).hom)).app (L.obj (DerivedCategory.Q.obj P)) ≫
      aS.ell.hom.app (L.obj (DerivedCategory.Q.obj P)) =
        L.map (aR.ell.hom.app (DerivedCategory.Q.obj P)) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  let U := HomologicalComplex.tensorUnit (MR) (.up ℤ)
  let V := HomologicalComplex.tensorUnit (MS) (.up ℤ)
  let F := pullF
  let j : F.obj U ⟶ V :=
    (CategoryTheory.CochainPullback.unit (R := R) (S := S) f k).hom
  let lP : ((tR₀).obj U).obj P ⟶ P := (HomologicalComplex.leftUnitor P).hom
  let lFP : ((tS₀).obj V).obj (F.obj P) ⟶ F.obj P :=
    (HomologicalComplex.leftUnitor (F.obj P)).hom
  let c : F.obj (((tR₀).obj U).obj P) ⟶
      ((tS₀).obj (F.obj U)).obj (F.obj P) := (comparison f k U P).hom
  obtain ⟨hu', hp', huf', hf', hnorm⟩ := hm U P aR.unit_kflat hp aR.unit_flat hf
  change _ = epsilon.app (((tR₀).obj U).obj P) ≫ DerivedCategory.Q.map c ≫
    (canonicalRepresentativeIso S (F.obj U) (F.obj P) hu' hp' huf' hf').hom at hnorm
  obtain ⟨cL, _, hcL⟩ := (hcS (F.obj P) hp' hf').2
  have hn := cL.hom.naturality j
  change DerivedCategory.Q.map (((tS₀).map j).app (F.obj P)) ≫
    (cL.app V).hom = (cL.app (F.obj U)).hom ≫
      ((TS).map (DerivedCategory.Q.map j)).app (DerivedCategory.Q.obj (F.obj P)) at hn
  erw [hcL V aS.unit_kflat aS.unit_flat, hcL (F.obj U) hu' huf'] at hn
  have hunit :
      (canonicalRepresentativeIso.{uD, vD, r, wS} S (F.obj U) (F.obj P) hu' hp' huf' hf').hom ≫
          ((TS).map (DerivedCategory.Q.map j)).app
            (DerivedCategory.Q.obj (F.obj P)) ≫
          aS.ell.hom.app (DerivedCategory.Q.obj (F.obj P)) =
        DerivedCategory.Q.map
          (((tS₀).map j).app (F.obj P) ≫
            lFP) := by
    erw [← Category.assoc, ← hn, Category.assoc, aS.ell_normalized,
      ← Functor.map_comp]
  have hchain : F.map lP = c ≫
      ((tS₀).map j).app (F.obj P) ≫ lFP :=
    (cochainComparison_monoidal.{r, uC, vC, uD, vD} f k).2.2.2.1 P
  have heps := epsilon.naturality lP
  have hcomm : epsilon.app (((tR₀).obj U).obj P) ≫ DerivedCategory.Q.map c ≫
      DerivedCategory.Q.map (((tS₀).map j).app (F.obj P) ≫ lFP) =
        L.map (DerivedCategory.Q.map lP) ≫ epsilon.app P := by
    rw [← DerivedCategory.Q.map_comp, ← hchain]
    exact heps.symm
  exact normalized_left_unit_diagram L (TS) (DerivedCategory.Q.obj V) aS.ell.hom
    (canonicalRepresentativeIso R U P aR.unit_kflat hp aR.unit_flat hf).hom
    (aR.ell.hom.app (DerivedCategory.Q.obj P)) (DerivedCategory.Q.map lP)
    (mu.hom.app (DerivedCategory.Q.obj U, DerivedCategory.Q.obj P))
    (epsilon.app U) (epsilon.app P) (DerivedCategory.Q.map j)
    (epsilon.app (((tR₀).obj U).obj P)) (DerivedCategory.Q.map c)
    (canonicalRepresentativeIso S (F.obj U) (F.obj P) hu' hp' huf' hf').hom
    (DerivedCategory.Q.map (((tS₀).map j).app (F.obj P) ≫ lFP))
    (aR.ell_normalized P hp hf) hnorm hunit hcomm


private theorem leftUnit_equation
    [(DR).CommShift₂Int] [(DS).CommShift₂Int]
    (hcS : HasCanonicalTensorShifts (R := S))
    (aR : ActionUnits (R := R)) (aS : ActionUnits (R := S))
    (mu : Phi L ≅ Psi L) (hm : IsNormalized f k L epsilon mu.hom)
    (hL : L.IsLeftDerivedFunctor epsilon
      (HomologicalComplex.quasiIso (MR) (.up ℤ)))
    (u : L.obj (DerivedCategory.Q.obj
        (HomologicalComplex.tensorUnit (MR) (.up ℤ))) ≅
      DerivedCategory.Q.obj (HomologicalComplex.tensorUnit (MS) (.up ℤ)))
    (hu : u.hom = epsilon.app (HomologicalComplex.tensorUnit (MR) (.up ℤ)) ≫
      DerivedCategory.Q.map (CategoryTheory.CochainPullback.unit
        (R := R) (S := S) f k).hom) :
    ∀ M, mu.hom.app
        (DerivedCategory.Q.obj (HomologicalComplex.tensorUnit (MR) (.up ℤ)), M) ≫
      ((TS).map u.hom).app (L.obj M) ≫ aS.ell.hom.app (L.obj M) =
        L.map (aR.ell.hom.app M) := by
  let a := fixedLeftComparison L mu
      (DerivedCategory.Q.obj (HomologicalComplex.tensorUnit (MR) (.up ℤ))) ≫
    Functor.whiskerLeft L ((TS).map u.hom) ≫
    Functor.whiskerLeft L aS.ell.hom
  let b := Functor.whiskerRight aR.ell.hom L
  have hab : a = b := by
    apply derivedNatTrans_ext (R := R) (S := S)
    intro P hp hf
    change mu.hom.app _ ≫ _ ≫ _ = _
    rw [hu]
    exact leftUnit_representative f k L epsilon hcS aR aS mu hm P hp hf
      (PullbackTensorResolving.pullback_resolving_computation f L epsilon hL P hp hf)
  exact fun M ↦ NatTrans.congr_app hab M


attribute [local irreducible] HasCanonicalTensorShifts IsNormalized

set_option maxHeartbeats 1000000 in
-- The statement combines independently sized derived and total-tensor presentations.
/-- Canonical derived pullback tensor comparison, coherent with both integer
shifts and both normalized tensor action units, for arbitrary ringed topoi.
The universal left-derived comparison is written on complexes rather than the
homotopy category; localization through homotopy identifies the two formulations.
No derived direct image, derived adjunction or projection mate is part of the data.
Source: Stacks 06YY, 07A4, 0FNH (item-shift-tensor), and 03EL
(blueprint: lem-weil-pbc-pullback-tensor-canonical-shift-unit).

Proof plan, following the node's eight steps:
1. Use lem-weil-pbc-site-derived-tensor-descent to test transformations on
   flat-term K-flat representatives. The computation epsilon is natural and
   invertible there by lem-weil-pbc-ringed-topoi-derived-pullback. Shifting a
   representative preserves the resolving class by the fixed-tensor lemma;
   termwise pullback has identity shift maps and differential (-1)^n f*(d).
2. Use lem-pur-kflat-total-tensor-model and the canonical tensor-pullback lemma
   to compute epsilon on the total tensor. Compose the representative maps in
   IsNormalized. Tensor descent extends these components uniquely, and detects
   their invertibility. Descend the ordinary action unitors in the same way.
3. The first-input chain shift square is unsigned: on each summand both
   composites send b tensor (x tensor y) to (b tensor x) tensor (1 tensor y).
4. The second-input square contributes (-1)^(np) on both sides, where p is
   the first input degree. Pullback is additive, so it preserves this sign.
   lem-pur-cochain-pullback-tensor-coherence supplies the chain comparison.
5. The identity termwise shift maps and the signed total shifts satisfy zero
   and addition laws (lem-weil-pbc-total-tensor-integer-shifts). Conjugation by
   computation maps preserves these laws, giving the stated CommShift data.
6. R[0] is K-flat with flat terms: tensoring with it is the identity. Its
   pullback unit sends b tensor a to b c(a), inverse b to b tensor 1.
   Compose its localization with epsilon to obtain the normalized u.
7. For the right action, b tensor (x tensor a) goes to
   (b tensor x) tensor (1 tensor a), then to b c(a) tensor x = b tensor ax.
   For the left action, b tensor (a tensor y) goes to b c(a) tensor y =
   b tensor ay. These are the pulled-back action maps; the degree-zero ring
   factor contributes no sign. Apply localization and computation comparisons.
8. Faithful restriction from tensor descent proves both shift squares and both
   action equations globally. Naturality holds for complex maps, then inverse
   quasi-isomorphisms by rearranging their squares, and all localized composites.
   No boundedness or flatness of the structural ring map is used.
-/
theorem pullback_tensor_canonical_shift_unit
    (hL : L.IsLeftDerivedFunctor epsilon
      (HomologicalComplex.quasiIso (MR) (ComplexShape.up ℤ))) :
    ∃ (_ : L.CommShift ℤ) (_ : (DR).CommShift₂Int)
      (_ : (DS).CommShift₂Int),
      NatTrans.CommShift epsilon ℤ ∧
      HasCanonicalTensorShifts (R := R) ∧ HasCanonicalTensorShifts (R := S) ∧
      (∀ (P : CochainComplex (MR) ℤ), P.IsKFlatIndependentCoefficients →
        (∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)) → IsIso (epsilon.app P)) ∧
      ∃ mu : Phi L ≅ Psi L,
        IsNormalized f k L epsilon mu.hom ∧
        (∀ tau : Phi L ⟶ Psi L, IsNormalized f k L epsilon tau → tau = mu.hom) ∧
        ∃ (aR : ActionUnits (R := R)) (aS : ActionUnits (R := S))
          (u : L.obj (DerivedCategory.Q.obj (HomologicalComplex.tensorUnit (MR) (.up ℤ))) ≅
            DerivedCategory.Q.obj (HomologicalComplex.tensorUnit (MS) (.up ℤ))),
          Subsingleton (ActionUnits (R := R)) ∧ Subsingleton (ActionUnits (R := S)) ∧
          u.hom = epsilon.app (HomologicalComplex.tensorUnit (MR) (.up ℤ)) ≫
            DerivedCategory.Q.map
              (CategoryTheory.CochainPullback.unit.{r, uC, vC, uD, vD}
                (J := J) (K := K) (R := R) (S := S) f k).hom ∧
          (∀ (n : ℤ) (M N : DerivedCategory (MR)),
            mu.hom.app (M⟦n⟧, N) ≫
                ((TS).map ((L.commShiftIso n).hom.app M)).app (L.obj N) ≫
                (((TS).flip.obj (L.obj N)).commShiftIso n).hom.app (L.obj M) =
              L.map ((((TR).flip.obj N).commShiftIso n).hom.app M) ≫
                (L.commShiftIso n).hom.app (((TR).obj M).obj N) ≫
                (mu.hom.app (M, N))⟦n⟧') ∧
          (∀ (n : ℤ) (M N : DerivedCategory (MR)),
            mu.hom.app (M, N⟦n⟧) ≫
                ((TS).obj (L.obj M)).map ((L.commShiftIso n).hom.app N) ≫
                (((TS).obj (L.obj M)).commShiftIso n).hom.app (L.obj N) =
              L.map ((((TR).obj M).commShiftIso n).hom.app N) ≫
                (L.commShiftIso n).hom.app (((TR).obj M).obj N) ≫
                (mu.hom.app (M, N))⟦n⟧') ∧
          (∀ M : DerivedCategory (MR),
            mu.hom.app
                (M, DerivedCategory.Q.obj (HomologicalComplex.tensorUnit (MR) (.up ℤ))) ≫
                ((TS).obj (L.obj M)).map u.hom ≫ aS.rho.hom.app (L.obj M) =
              L.map (aR.rho.hom.app M)) ∧
          (∀ N : DerivedCategory (MR),
            mu.hom.app
                (DerivedCategory.Q.obj (HomologicalComplex.tensorUnit (MR) (.up ℤ)), N) ≫
                ((TS).map u.hom).app (L.obj N) ≫ aS.ell.hom.app (L.obj N) =
              L.map (aR.ell.hom.app N)) := by
  classical
  obtain ⟨sR, hcR⟩ := canonicalTensorShifts_exists.{uC, vC, r, wR} (R := R)
  obtain ⟨sS, hcS⟩ := canonicalTensorShifts_exists.{uD, vD, r, wS} (R := S)
  let _ : (DR).CommShift₂Int := sR
  let _ : (DS).CommShift₂Int := sS
  obtain ⟨sL, heps⟩ := Functor.rightKanExtension_coherentShift
    (pullF ⋙ DerivedCategory.Q) DerivedCategory.Q L epsilon
    hL.isRightKanExtension
  let _ : L.CommShift ℤ := sL
  refine ⟨sL, sR, sS, heps, hcR, hcS, ?_, ?_⟩
  · exact PullbackTensorResolving.pullback_resolving_computation f L epsilon hL
  · obtain ⟨mu, hmu, huniq⟩ := normalized_comparison.{uC, vC, uD, vD, r, wR, wS}
      f k L epsilon hcR hcS hL
    refine ⟨mu, hmu, huniq, ?_⟩
    let aR : ActionUnits (R := R) := Classical.choice
      (actionUnits_exists.{uC, vC, r, wR} (R := R) hcR)
    let aS : ActionUnits (R := S) := Classical.choice
      (actionUnits_exists.{uD, vD, r, wS} (R := S) hcS)
    have heU := PullbackTensorResolving.pullback_resolving_computation f L epsilon hL
      (HomologicalComplex.tensorUnit (MR) (.up ℤ)) aR.unit_kflat aR.unit_flat
    let u := asIso (epsilon.app (HomologicalComplex.tensorUnit (MR) (.up ℤ))) ≪≫
      DerivedCategory.Q.mapIso (CategoryTheory.CochainPullback.unit
        (R := R) (S := S) f k)
    refine ⟨aR, aS, u, actionUnits_subsingleton, actionUnits_subsingleton, rfl, ?_, ?_, ?_, ?_⟩
    · intro n M N
      have : NatTrans.CommShift (fixedRight (TR) (TS) L mu.hom N) ℤ :=
        rightShift_global f k L epsilon hcR hcS mu hmu hL N
      exact fixedRight_shift_equation (TR) (TS) L mu.hom N n M
    · intro n M N
      have : NatTrans.CommShift (fixedLeft (TR) (TS) L mu.hom M) ℤ :=
        leftShift_global f k L epsilon hcR hcS mu hmu hL M
      exact fixedLeft_shift_equation (TR) (TS) L mu.hom M n N
    · exact rightUnit_equation f k L epsilon hcS aR aS mu hmu hL u rfl
    · exact leftUnit_equation f k L epsilon hcS aR aS mu hmu hL u rfl

end SheafOfModules.PullbackTensorCanonical

-- Restore Mathlib's original instance and priority for importing modules.
attribute [instance high] CategoryTheory.hasSheafCompose_of_preservesMulticospan

