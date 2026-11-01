/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPointStages
public import WeilConjectures.CategoryTheory.DerivedCategory.Field.FieldDerivedScalarTower
public import WeilConjectures.SmoothPurity.Coefficient.CoefficientComplexRationalization
public import WeilConjectures.SmoothPurity.Point.PointSectionsScalarExtension
public import WeilConjectures.TraceFormula.Integral.IntegralScalarOrdinaryModelCoherence

/-! # Further-extension invariance of the point-fibre representative

Source: the scalar-extension tower equation for point sections and the common-stage calculus.
(blueprint: lem-weil-point-fibre-representative-transport).
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

private theorem representative_transport
    {I : Type z} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
    (S : StageSystem C) {D : Type w} [Category D]
    (F : ∀ i, C i ⥤ D)
    (e : ∀ {i j : I} (h : i ≤ j), S.T h ⋙ F j ≅ F i)
    (he : ∀ {i j k : I} (h : i ≤ j) (k : j ≤ k) (X : C i),
      (F _).map ((S.assoc h k).hom.app X) ≫ (e (h.trans k)).hom.app X =
        (e k).hom.app ((S.T h).obj X) ≫ (e h).hom.app X)
    {i j n m : I} (X : C i) (Y : C j) (hi : i ≤ n) (hj : j ≤ n) (h : n ≤ m)
    (f : (S.T hi).obj X ⟶ (S.T hj).obj Y) :
    (e (hi.trans h)).inv.app X ≫ (F m).map (S.tr h f) ≫
        (e (hj.trans h)).hom.app Y =
      (e hi).inv.app X ≫ (F n).map f ≫ (e hj).hom.app Y := by
  apply (cancel_epi ((e hi).hom.app X)).mp
  simp -implicitDefEqProofs only [StageSystem.tr, Functor.map_comp, Category.assoc]
  have hx := he hi h X
  have hy := he hj h Y
  have hx' : (e hi).hom.app X ≫ (e (hi.trans h)).inv.app X ≫
      (F m).map ((S.assoc hi h).inv.app X) =
        (e h).inv.app ((S.T hi).obj X) := by
    apply (cancel_epi ((e h).hom.app ((S.T hi).obj X))).mp
    erw [← Category.assoc, ← hx]
    simp -implicitDefEqProofs only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp,
      Iso.hom_inv_id_app]
    exact (F m).map_id _
  erw [reassoc_of% hx', hy]
  have hn := (e h).hom.naturality f
  dsimp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  simp

private theorem normalizedTower
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (U₀ : C₀ ⥤ D₀) (U₁ : C₁ ⥤ D₁) (U₂ : C₂ ⥤ D₂)
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₀ ⥤ C₂)
    (V : D₀ ⥤ D₁) (W : D₁ ⥤ D₂) (J : D₀ ⥤ D₂)
    (tF : F ⋙ U₁ ≅ U₀ ⋙ V) (tG : G ⋙ U₂ ≅ U₁ ⋙ W)
    (tH : H ⋙ U₂ ≅ U₀ ⋙ J) (aF : F ⋙ G ≅ H) (aV : V ⋙ W ≅ J)
    (X : C₀) (Y : C₁) (Z Z' : C₂)
    (NX : D₀) (NY : D₁) (NZ NZ' : D₂)
    (nX : U₀.obj X ≅ NX) (nY : U₁.obj Y ≅ NY)
    (nZ : U₂.obj Z ≅ NZ) (nZ' : U₂.obj Z' ≅ NZ')
    (f : Y ⟶ F.obj X) (g : Z ⟶ G.obj Y) (h : Z' ⟶ H.obj X) (r : Z ⟶ Z')
    (sf : NY ⟶ V.obj NX) (sg : NZ ⟶ W.obj NY) (sh : NZ' ⟶ J.obj NX)
    (sr : NZ ⟶ NZ')
    (hf : U₁.map f ≫ tF.hom.app X ≫ V.map nX.hom = nY.hom ≫ sf)
    (hg : U₂.map g ≫ tG.hom.app Y ≫ W.map nY.hom = nZ.hom ≫ sg)
    (hh : U₂.map h ≫ tH.hom.app X ≫ J.map nX.hom = nZ'.hom ≫ sh)
    (hr : U₂.map r ≫ nZ'.hom = nZ.hom ≫ sr)
    (hs : sr ≫ sh = sg ≫ W.map sf ≫ aV.hom.app NX)
    (ht : U₂.map (aF.hom.app X) ≫ tH.hom.app X =
      tG.hom.app (F.obj X) ≫ W.map (tF.hom.app X) ≫ aV.hom.app (U₀.obj X)) :
    U₂.map (r ≫ h) = U₂.map (g ≫ G.map f ≫ aF.hom.app X) := by
  apply (cancel_mono (tH.hom.app X ≫ J.map nX.hom)).mp
  simp -implicitDefEqProofs only [Functor.map_comp, Category.assoc]
  erw [hh, reassoc_of% hr, hs, reassoc_of% ht]
  have hn := tG.hom.naturality f
  dsimp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  have ha := aV.hom.naturality nX.hom
  dsimp only [Functor.comp_map] at ha
  erw [← ha]
  have hc := congrArg W.map hf
  simp -implicitDefEqProofs only [Functor.map_comp] at hc
  erw [reassoc_of% hc, reassoc_of% hg]

private theorem mappedSquareTower
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (U₀ : C₀ ⥤ D₀) (U₁ : C₁ ⥤ D₁) (U₂ : C₂ ⥤ D₂)
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₀ ⥤ C₂)
    (V : D₀ ⥤ D₁) (W : D₁ ⥤ D₂) (J : D₀ ⥤ D₂)
    (tF : F ⋙ U₁ ≅ U₀ ⋙ V) (tG : G ⋙ U₂ ≅ U₁ ⋙ W)
    (tH : H ⋙ U₂ ≅ U₀ ⋙ J) (aF : F ⋙ G ≅ H) (aV : V ⋙ W ≅ J)
    (X : C₀) (Y : C₁) (Z Z' : C₂)
    (f : Y ⟶ F.obj X) (g : Z ⟶ G.obj Y) (h : Z' ⟶ H.obj X) (r : Z ⟶ Z')
    (hs : r ≫ h = g ≫ G.map f ≫ aF.hom.app X)
    (ht : U₂.map (aF.hom.app X) ≫ tH.hom.app X =
      tG.hom.app (F.obj X) ≫ W.map (tF.hom.app X) ≫ aV.hom.app (U₀.obj X)) :
    U₂.map r ≫ U₂.map h ≫ tH.hom.app X =
      U₂.map g ≫ tG.hom.app Y ≫ W.map (U₁.map f ≫ tF.hom.app X) ≫
        aV.hom.app (U₀.obj X) := by
  erw [← Functor.map_comp_assoc, hs]
  simp -implicitDefEqProofs only [Functor.map_comp, Category.assoc]
  erw [ht]
  have hn := tG.hom.naturality f
  dsimp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]

private theorem compositeTower
    {C₀ C₁ C₂ D₀ D₁ D₂ E : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂] [Category E]
    (T₁ : C₀ ⥤ C₁) (T₂ : C₁ ⥤ C₂) (T₃ : C₀ ⥤ C₂)
    (I₀ : C₀ ⥤ D₀) (I₁ : C₁ ⥤ D₁) (I₂ : C₂ ⥤ D₂)
    (V₁ : D₀ ⥤ D₁) (V₂ : D₁ ⥤ D₂) (V₃ : D₀ ⥤ D₂)
    (U₀ : D₀ ⥤ E) (U₁ : D₁ ⥤ E) (U₂ : D₂ ⥤ E)
    (a : T₁ ⋙ T₂ ≅ T₃) (b : V₁ ⋙ V₂ ≅ V₃)
    (p₁ : T₁ ⋙ I₁ ≅ I₀ ⋙ V₁) (p₂ : T₂ ⋙ I₂ ≅ I₁ ⋙ V₂)
    (p₃ : T₃ ⋙ I₂ ≅ I₀ ⋙ V₃)
    (q₁ : V₁ ⋙ U₁ ≅ U₀) (q₂ : V₂ ⋙ U₂ ≅ U₁) (q₃ : V₃ ⋙ U₂ ≅ U₀)
    (K : C₀)
    (hp : I₂.map (a.hom.app K) ≫ p₃.hom.app K =
      p₂.hom.app (T₁.obj K) ≫ V₂.map (p₁.hom.app K) ≫ b.hom.app (I₀.obj K))
    (hq : U₂.map (b.hom.app (I₀.obj K)) ≫ q₃.hom.app (I₀.obj K) =
      q₂.hom.app (V₁.obj (I₀.obj K)) ≫ q₁.hom.app (I₀.obj K)) :
    (I₂ ⋙ U₂).map (a.hom.app K) ≫ U₂.map (p₃.hom.app K) ≫ q₃.hom.app (I₀.obj K) =
      U₂.map (p₂.hom.app (T₁.obj K)) ≫ q₂.hom.app (I₁.obj (T₁.obj K)) ≫
        U₁.map (p₁.hom.app K) ≫ q₁.hom.app (I₀.obj K) := by
  simp -implicitDefEqProofs only [Functor.comp_map, ← Functor.map_comp_assoc]
  erw [hp]
  simp -implicitDefEqProofs only [Functor.map_comp, Category.assoc]
  erw [hq]
  have hn := q₂.hom.naturality (p₁.hom.app K)
  dsimp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]

private theorem towerHEqAll
    {C₀ C₁ C₂ C₀' C₁' C₂' : Type u} {D₀ D₁ D₂ D₀' D₁' D₂' : Type w}
    [c₀ : Category.{v} C₀] [c₁ : Category.{v} C₁] [c₂ : Category.{v} C₂]
    [c₀' : Category.{v} C₀'] [c₁' : Category.{v} C₁'] [c₂' : Category.{v} C₂']
    [d₀ : Category.{z} D₀] [d₁ : Category.{z} D₁] [d₂ : Category.{z} D₂]
    [d₀' : Category.{z} D₀'] [d₁' : Category.{z} D₁'] [d₂' : Category.{z} D₂']
    (hc₀ : C₀ = C₀') (hc₁ : C₁ = C₁') (hc₂ : C₂ = C₂')
    (hcat₀ : HEq c₀ c₀') (hcat₁ : HEq c₁ c₁') (hcat₂ : HEq c₂ c₂')
    (hd₀ : D₀ = D₀') (hd₁ : D₁ = D₁') (hd₂ : D₂ = D₂')
    (hdcat₀ : HEq d₀ d₀') (hdcat₁ : HEq d₁ d₁') (hdcat₂ : HEq d₂ d₂')
    (T₁ : C₀ ⥤ C₁) (T₂ : C₁ ⥤ C₂) (T₃ : C₀ ⥤ C₂)
    (F₁ : C₀' ⥤ C₁') (F₂ : C₁' ⥤ C₂') (F₃ : C₀' ⥤ C₂')
    (R₀ : C₀ ⥤ D₀) (R₁ : C₁ ⥤ D₁) (R₂ : C₂ ⥤ D₂)
    (S₀ : C₀' ⥤ D₀') (S₁ : C₁' ⥤ D₁') (S₂ : C₂' ⥤ D₂')
    (M₁ : D₀ ⥤ D₁) (M₂ : D₁ ⥤ D₂) (M₃ : D₀ ⥤ D₂)
    (N₁ : D₀' ⥤ D₁') (N₂ : D₁' ⥤ D₂') (N₃ : D₀' ⥤ D₂')
    (aT : T₁ ⋙ T₂ ≅ T₃) (a : F₁ ⋙ F₂ ≅ F₃)
    (e₁ : T₁ ⋙ R₁ ≅ R₀ ⋙ M₁) (e₂ : T₂ ⋙ R₂ ≅ R₁ ⋙ M₂)
    (e₃ : T₃ ⋙ R₂ ≅ R₀ ⋙ M₃)
    (p₁ : F₁ ⋙ S₁ ≅ S₀ ⋙ N₁) (p₂ : F₂ ⋙ S₂ ≅ S₁ ⋙ N₂)
    (p₃ : F₃ ⋙ S₂ ≅ S₀ ⋙ N₃) (b : M₁ ⋙ M₂ ≅ M₃)
    (b' : N₁ ⋙ N₂ ≅ N₃)
    (ht₁ : HEq T₁ F₁) (ht₂ : HEq T₂ F₂) (ht₃ : HEq T₃ F₃)
    (hr₀ : HEq R₀ S₀) (hr₁ : HEq R₁ S₁) (hr₂ : HEq R₂ S₂)
    (hm₁ : HEq M₁ N₁) (hm₂ : HEq M₂ N₂) (hm₃ : HEq M₃ N₃)
    (hb : HEq b b') (ha : HEq aT a) (he₁ : HEq e₁ p₁) (he₂ : HEq e₂ p₂) (he₃ : HEq e₃ p₃)
    (K : C₀) (K' : C₀') (hk : HEq K K')
    (h : S₂.map (a.hom.app K') ≫ p₃.hom.app K' =
      p₂.hom.app (F₁.obj K') ≫ N₂.map (p₁.hom.app K') ≫ b'.hom.app (S₀.obj K')) :
    R₂.map (aT.hom.app K) ≫ e₃.hom.app K =
      e₂.hom.app (T₁.obj K) ≫ M₂.map (e₁.hom.app K) ≫ b.hom.app (R₀.obj K) := by
  subst C₀'
  subst C₁'
  subst C₂'
  subst D₀'
  subst D₁'
  subst D₂'
  cases eq_of_heq hdcat₀
  cases eq_of_heq hdcat₁
  cases eq_of_heq hdcat₂
  cases eq_of_heq hcat₀
  cases eq_of_heq hcat₁
  cases eq_of_heq hcat₂
  cases eq_of_heq ht₁
  cases eq_of_heq ht₂
  cases eq_of_heq ht₃
  cases eq_of_heq hr₀
  cases eq_of_heq hr₁
  cases eq_of_heq hr₂
  cases eq_of_heq hm₁
  cases eq_of_heq hm₂
  cases eq_of_heq hm₃
  cases eq_of_heq hb
  cases eq_of_heq ha
  cases eq_of_heq he₁
  cases eq_of_heq he₂
  cases eq_of_heq he₃
  cases eq_of_heq hk
  exact h

private theorem whiskerRight_transport_heq
    {C D E : Type*} [Category C] [Category D] [Category E]
    {T F : C ⥤ D} (h : T = F) (R : D ⥤ E) (S : C ⥤ E) (p : F ⋙ R ≅ S) :
    HEq (Functor.isoWhiskerRight (eqToIso h) R ≪≫ p) p := by
  subst F
  apply heq_of_eq
  ext X
  simp

private noncomputable def liftedComparison
    {C₀ C₁ D₀ D₁ E₀ E₁ : Type*}
    [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    [Category E₀] [Category E₁]
    (T : C₀ ⥤ C₁) (R₀ : C₀ ⥤ D₀) (R₁ : C₁ ⥤ D₁) (F : D₀ ⥤ D₁)
    (U₀ : D₀ ⥤ E₀) (U₁ : D₁ ⥤ E₁) (V : E₀ ⥤ E₁)
    (p : T ⋙ R₁ ≅ R₀ ⋙ F) (q : F ⋙ U₁ ≅ U₀ ⋙ V) :
    T ⋙ (R₁ ⋙ U₁) ≅ (R₀ ⋙ U₀) ⋙ V :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight p U₁ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft R₀ q ≪≫
    (Functor.associator _ _ _).symm

private theorem liftedComparison_hom
    {C₀ C₁ D₀ D₁ E₀ E₁ : Type*}
    [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    [Category E₀] [Category E₁]
    (T : C₀ ⥤ C₁) (R₀ : C₀ ⥤ D₀) (R₁ : C₁ ⥤ D₁) (F : D₀ ⥤ D₁)
    (U₀ : D₀ ⥤ E₀) (U₁ : D₁ ⥤ E₁) (V : E₀ ⥤ E₁)
    (p : T ⋙ R₁ ≅ R₀ ⋙ F) (q : F ⋙ U₁ ≅ U₀ ⋙ V) (K : C₀) :
    (liftedComparison T R₀ R₁ F U₀ U₁ V p q).hom.app K =
      U₁.map (p.hom.app K) ≫ q.hom.app (R₀.obj K) := by
  simp -implicitDefEqProofs only [liftedComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Category.id_comp, Category.comp_id]

private theorem liftedTower
    {C₀ C₁ C₂ D₀ D₁ D₂ E₀ E₁ E₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    [Category E₀] [Category E₁] [Category E₂]
    (T₁ : C₀ ⥤ C₁) (T₂ : C₁ ⥤ C₂) (T₃ : C₀ ⥤ C₂)
    (R₀ : C₀ ⥤ D₀) (R₁ : C₁ ⥤ D₁) (R₂ : C₂ ⥤ D₂)
    (F₁ : D₀ ⥤ D₁) (F₂ : D₁ ⥤ D₂) (F₃ : D₀ ⥤ D₂)
    (U₀ : D₀ ⥤ E₀) (U₁ : D₁ ⥤ E₁) (U₂ : D₂ ⥤ E₂)
    (V₁ : E₀ ⥤ E₁) (V₂ : E₁ ⥤ E₂) (V₃ : E₀ ⥤ E₂)
    (a : T₁ ⋙ T₂ ≅ T₃) (b : F₁ ⋙ F₂ ≅ F₃) (c : V₁ ⋙ V₂ ≅ V₃)
    (p₁ : T₁ ⋙ R₁ ≅ R₀ ⋙ F₁) (p₂ : T₂ ⋙ R₂ ≅ R₁ ⋙ F₂)
    (p₃ : T₃ ⋙ R₂ ≅ R₀ ⋙ F₃)
    (q₁ : F₁ ⋙ U₁ ≅ U₀ ⋙ V₁) (q₂ : F₂ ⋙ U₂ ≅ U₁ ⋙ V₂)
    (q₃ : F₃ ⋙ U₂ ≅ U₀ ⋙ V₃)
    (A₀ : C₀ ⥤ E₀) (A₁ : C₁ ⥤ E₁) (A₂ : C₂ ⥤ E₂)
    (hA₀ : A₀ = R₀ ⋙ U₀) (hA₁ : A₁ = R₁ ⋙ U₁) (hA₂ : A₂ = R₂ ⋙ U₂)
    (e₁ : T₁ ⋙ A₁ ≅ A₀ ⋙ V₁) (e₂ : T₂ ⋙ A₂ ≅ A₁ ⋙ V₂)
    (e₃ : T₃ ⋙ A₂ ≅ A₀ ⋙ V₃)
    (he₁ : HEq e₁ (liftedComparison T₁ R₀ R₁ F₁ U₀ U₁ V₁ p₁ q₁))
    (he₂ : HEq e₂ (liftedComparison T₂ R₁ R₂ F₂ U₁ U₂ V₂ p₂ q₂))
    (he₃ : HEq e₃ (liftedComparison T₃ R₀ R₂ F₃ U₀ U₂ V₃ p₃ q₃))
    (K : C₀)
    (hp : R₂.map (a.hom.app K) ≫ p₃.hom.app K =
      p₂.hom.app (T₁.obj K) ≫ F₂.map (p₁.hom.app K) ≫ b.hom.app (R₀.obj K))
    (hq : U₂.map (b.hom.app (R₀.obj K)) ≫ q₃.hom.app (R₀.obj K) =
      q₂.hom.app (F₁.obj (R₀.obj K)) ≫ V₂.map (q₁.hom.app (R₀.obj K)) ≫
        c.hom.app (U₀.obj (R₀.obj K))) :
    A₂.map (a.hom.app K) ≫ e₃.hom.app K =
      e₂.hom.app (T₁.obj K) ≫ V₂.map (e₁.hom.app K) ≫ c.hom.app (A₀.obj K) := by
  subst A₀
  subst A₁
  subst A₂
  erw [eq_of_heq he₁, eq_of_heq he₂, eq_of_heq he₃]
  simpa -implicitDefEqProofs only [liftedComparison_hom, Functor.comp_map, Functor.comp_obj,
    Functor.map_comp, Category.assoc]
    using! mappedSquareTower U₀ U₁ U₂ F₁ F₂ F₃ V₁ V₂ V₃ q₁ q₂ q₃ b c
      (R₀.obj K) (R₁.obj (T₁.obj K)) (R₂.obj (T₂.obj (T₁.obj K))) (R₂.obj (T₃.obj K))
      (p₁.hom.app K) (p₂.hom.app (T₁.obj K)) (p₃.hom.app K)
      (R₂.map (a.hom.app K)) hp hq

private noncomputable def finishedComparison
    {C₀ C₁ D₀ D₁ E : Type*}
    [Category C₀] [Category C₁] [Category D₀] [Category D₁] [Category E]
    (T : C₀ ⥤ C₁) (R₀ : C₀ ⥤ D₀) (R₁ : C₁ ⥤ D₁) (V : D₀ ⥤ D₁)
    (U₀ : D₀ ⥤ E) (U₁ : D₁ ⥤ E)
    (p : T ⋙ R₁ ≅ R₀ ⋙ V) (q : V ⋙ U₁ ≅ U₀) :
    T ⋙ (R₁ ⋙ U₁) ≅ R₀ ⋙ U₀ :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight p U₁ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft R₀ q

private theorem finishedComparison_hom
    {C₀ C₁ D₀ D₁ E : Type*}
    [Category C₀] [Category C₁] [Category D₀] [Category D₁] [Category E]
    (T : C₀ ⥤ C₁) (R₀ : C₀ ⥤ D₀) (R₁ : C₁ ⥤ D₁) (V : D₀ ⥤ D₁)
    (U₀ : D₀ ⥤ E) (U₁ : D₁ ⥤ E)
    (p : T ⋙ R₁ ≅ R₀ ⋙ V) (q : V ⋙ U₁ ≅ U₀) (K : C₀) :
    (finishedComparison T R₀ R₁ V U₀ U₁ p q).hom.app K =
      U₁.map (p.hom.app K) ≫ q.hom.app (R₀.obj K) := by
  simp -implicitDefEqProofs only [finishedComparison, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Category.id_comp]

private theorem finishedComparison_inv
    {C₀ C₁ D₀ D₁ E : Type*}
    [Category C₀] [Category C₁] [Category D₀] [Category D₁] [Category E]
    (T : C₀ ⥤ C₁) (R₀ : C₀ ⥤ D₀) (R₁ : C₁ ⥤ D₁) (V : D₀ ⥤ D₁)
    (U₀ : D₀ ⥤ E) (U₁ : D₁ ⥤ E)
    (p : T ⋙ R₁ ≅ R₀ ⋙ V) (q : V ⋙ U₁ ≅ U₀) (K : C₀) :
    (finishedComparison T R₀ R₁ V U₀ U₁ p q).inv.app K =
      q.inv.app (R₀.obj K) ≫ U₁.map (p.inv.app K) := by
  simp -implicitDefEqProofs only [finishedComparison, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Category.comp_id]

private theorem finishedTower
    {C₀ C₁ C₂ D₀ D₁ D₂ E : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂] [Category E]
    (T₁ : C₀ ⥤ C₁) (T₂ : C₁ ⥤ C₂) (T₃ : C₀ ⥤ C₂)
    (I₀ : C₀ ⥤ D₀) (I₁ : C₁ ⥤ D₁) (I₂ : C₂ ⥤ D₂)
    (V₁ : D₀ ⥤ D₁) (V₂ : D₁ ⥤ D₂) (V₃ : D₀ ⥤ D₂)
    (U₀ : D₀ ⥤ E) (U₁ : D₁ ⥤ E) (U₂ : D₂ ⥤ E)
    (a : T₁ ⋙ T₂ ≅ T₃) (b : V₁ ⋙ V₂ ≅ V₃)
    (p₁ : T₁ ⋙ I₁ ≅ I₀ ⋙ V₁) (p₂ : T₂ ⋙ I₂ ≅ I₁ ⋙ V₂)
    (p₃ : T₃ ⋙ I₂ ≅ I₀ ⋙ V₃)
    (q₁ : V₁ ⋙ U₁ ≅ U₀) (q₂ : V₂ ⋙ U₂ ≅ U₁) (q₃ : V₃ ⋙ U₂ ≅ U₀)
    (K : C₀)
    (hp : I₂.map (a.hom.app K) ≫ p₃.hom.app K =
      p₂.hom.app (T₁.obj K) ≫ V₂.map (p₁.hom.app K) ≫ b.hom.app (I₀.obj K))
    (hq : U₂.map (b.hom.app (I₀.obj K)) ≫ q₃.hom.app (I₀.obj K) =
      q₂.hom.app (V₁.obj (I₀.obj K)) ≫ q₁.hom.app (I₀.obj K)) :
    (I₂ ⋙ U₂).map (a.hom.app K) ≫
        (finishedComparison T₃ I₀ I₂ V₃ U₀ U₂ p₃ q₃).hom.app K =
      (finishedComparison T₂ I₁ I₂ V₂ U₁ U₂ p₂ q₂).hom.app (T₁.obj K) ≫
        (finishedComparison T₁ I₀ I₁ V₁ U₀ U₁ p₁ q₁).hom.app K := by
  simpa -implicitDefEqProofs only [finishedComparison_hom, Category.assoc] using!
    compositeTower T₁ T₂ T₃ I₀ I₁ I₂ V₁ V₂ V₃ U₀ U₁ U₂ a b p₁ p₂ p₃ q₁ q₂ q₃ K hp hq

private theorem finishedRepresentative_transport
    {I : Type*} [Preorder I] {C : I → Type*} [∀ i, Category (C i)]
    (S : StageSystem C) {D : I → Type*} [∀ i, Category (D i)]
    {E : Type*} [Category E]
    (R : ∀ i, C i ⥤ D i) (U : ∀ i, D i ⥤ E)
    (V : ∀ {i j : I}, i ≤ j → D i ⥤ D j)
    (p : ∀ {i j : I} (h : i ≤ j), S.T h ⋙ R j ≅ R i ⋙ V h)
    (q : ∀ {i j : I} (h : i ≤ j), V h ⋙ U j ≅ U i)
    (he : ∀ {i j k : I} (h : i ≤ j) (k : j ≤ k) (X : C i),
      (R _ ⋙ U _).map ((S.assoc h k).hom.app X) ≫
          (finishedComparison (S.T (h.trans k)) (R i) (R _) (V (h.trans k))
            (U i) (U _) (p (h.trans k)) (q (h.trans k))).hom.app X =
        (finishedComparison (S.T k) (R j) (R _) (V k) (U j) (U _) (p k) (q k)).hom.app
            ((S.T h).obj X) ≫
          (finishedComparison (S.T h) (R i) (R j) (V h) (U i) (U j) (p h) (q h)).hom.app X)
    {i j n m : I} (X : C i) (Y : C j) (hi : i ≤ n) (hj : j ≤ n) (h : n ≤ m)
    (f : (S.T hi).obj X ⟶ (S.T hj).obj Y) :
    (q (hi.trans h)).inv.app ((R i).obj X) ≫
        (U m).map ((p (hi.trans h)).inv.app X ≫ (R m).map (S.tr h f) ≫
          (p (hj.trans h)).hom.app Y) ≫ (q (hj.trans h)).hom.app ((R j).obj Y) =
      (q hi).inv.app ((R i).obj X) ≫
        (U n).map ((p hi).inv.app X ≫ (R n).map f ≫ (p hj).hom.app Y) ≫
        (q hj).hom.app ((R j).obj Y) := by
  simpa -implicitDefEqProofs only [finishedComparison_hom, finishedComparison_inv, Functor.comp_map,
    Functor.map_comp, Category.assoc] using! representative_transport S
      (fun i ↦ R i ⋙ U i)
      (fun h ↦ finishedComparison (S.T h) (R _) (R _) (V h) (U _) (U _) (p h) (q h))
      (fun h k X ↦ he h k X) X Y hi hj h f

private theorem appHEq
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (a : F ⟶ G) {X Y : C} (h : X = Y) : HEq (a.app X) (a.app Y) := by
  subst Y
  rfl

private theorem isoThree
    {C D : Type*} [Category C] [Category D]
    {F G H J : C ⥤ D} (a : F ≅ G) (b : G ≅ H) (c : H ≅ J) (X : C) :
    (a ≪≫ b ≪≫ c).hom.app X = a.hom.app X ≫ b.hom.app X ≫ c.hom.app X := by
  simp -implicitDefEqProofs only [Iso.trans_hom, NatTrans.comp_app]

private theorem fullSubcategory_comp_three
    {C : Type*} [Category C] (P : ObjectProperty C)
    {A B C' D : P.FullSubcategory}
    (f : A ⟶ B) (g : B ⟶ C') (h : C' ⟶ D)
    (f' : A.obj ⟶ B.obj) (g' : B.obj ⟶ C'.obj) (h' : C'.obj ⟶ D.obj)
    (hf : f.hom = f') (hg : g.hom = g') (hh : h.hom = h') :
    (f ≫ g ≫ h).hom = f' ≫ g' ≫ h' := by
  simp -implicitDefEqProofs only [ObjectProperty.FullSubcategory.comp_hom, hf, hg, hh]

private theorem fullSubcategory_two_three
    {C : Type*} [Category C] (P : ObjectProperty C)
    {A B D E F : P.FullSubcategory}
    (a : A ⟶ B) (b : B ⟶ F) (c : A ⟶ D) (d : D ⟶ E) (e : E ⟶ F)
    (a' : A.obj ⟶ B.obj) (b' : B.obj ⟶ F.obj)
    (c' : A.obj ⟶ D.obj) (d' : D.obj ⟶ E.obj) (e' : E.obj ⟶ F.obj)
    (ha : a.hom = a') (hb : b.hom = b') (hc : c.hom = c')
    (hd : d.hom = d') (he : e.hom = e') (h : a' ≫ b' = c' ≫ d' ≫ e') :
    a ≫ b = c ≫ d ≫ e := by
  apply ObjectProperty.hom_ext
  simpa -implicitDefEqProofs only
    [ObjectProperty.FullSubcategory.comp_hom, ha, hb, hc, hd, he] using! h

private noncomputable def scalarSquare
    (f : R →+* S) (g : R' →+* S') (r : R →+* R') (s : S →+* S')
    (h : s.comp f = g.comp r) :
    ModuleCat.extendScalars.{u, u, u} f ⋙ ModuleCat.extendScalars s ≅
      ModuleCat.extendScalars r ⋙ ModuleCat.extendScalars g :=
  (ModuleCat.extendScalarsComp.{u, u} f s).symm ≪≫
    eqToIso (congrArg (ModuleCat.extendScalars.{u, u, u}) h) ≪≫
    ModuleCat.extendScalarsComp.{u, u} r g

private theorem scalarTransport_tmul {R S : Type u} [CommRing R] [CommRing S]
    (f g : R →+* S) (h : f = g) (P : ModuleCat.{max u v} R) (s : S) (n : P) :
    (eqToIso (congrArg (ModuleCat.extendScalars.{u, u, max u v}) h)).hom.app P
      (s ⊗ₜ[R, f] n) = s ⊗ₜ[R, g] n := by
  subst g
  rfl

private theorem scalarSquare_one
    (f : R →+* S) (g : R' →+* S') (r : R →+* R') (s : S →+* S')
    (h : s.comp f = g.comp r) (P : ModuleCat.{u} R) (x : P) :
    (scalarSquare f g r s h).hom.app P
      ((1 : S') ⊗ₜ[S, s] ((1 : S) ⊗ₜ[R, f] x)) =
      (1 : S') ⊗ₜ[R', g]
        (show (ModuleCat.extendScalars.{u, u, u} r).obj P from
          (1 : R') ⊗ₜ[R, r] x) := by
  simp -implicitDefEqProofs only [scalarSquare, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    ModuleCat.comp_apply]
  erw [scalarComp_inv_tmul.{u, u} f s P 1 1 x]
  simp -implicitDefEqProofs only [map_one, mul_one]
  erw [scalarTransport_tmul.{u, u} (s.comp f) (g.comp r) h P 1 x,
    scalarComp_hom_tmul.{u, u} r g P 1 x]
  with_unfolding_all rfl

private theorem scalarTriple_hom_ext {R S T U : Type u}
    [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    (f : R →+* S) (g : S →+* T) (k : T →+* U)
    (P : ModuleCat.{max u v} R) (X : ModuleCat.{max u v} U)
    (α β : (ModuleCat.extendScalars k).obj
      ((ModuleCat.extendScalars g).obj ((ModuleCat.extendScalars f).obj P)) ⟶ X)
    (h : ∀ n : P, α ((1 : U) ⊗ₜ[T, k] ((1 : T) ⊗ₜ[S, g]
        ((1 : S) ⊗ₜ[R, f] n))) =
      β ((1 : U) ⊗ₜ[T, k] ((1 : T) ⊗ₜ[S, g] ((1 : S) ⊗ₜ[R, f] n)))) :
    α = β := by
  apply ((ModuleCat.extendRestrictScalarsAdj k).homEquiv _ _).injective
  apply scalarDouble_hom_ext
  intro n
  exact h n

private theorem scalarSquare_tower
    (f : R →+* S) (j : S →+* T) (g : R' →+* S') (k : S' →+* T')
    (r : R →+* R') (s : S →+* S') (t : T →+* T')
    (h01 : s.comp f = g.comp r) (h12 : t.comp j = k.comp s)
    (h02 : t.comp (j.comp f) = (k.comp g).comp r) :
    Functor.isoWhiskerRight (ModuleCat.extendScalarsComp.{u, u} f j).symm
        (ModuleCat.extendScalars t) ≪≫ scalarSquare (j.comp f) (k.comp g) r t h02 =
    Functor.isoWhiskerLeft (ModuleCat.extendScalars f) (scalarSquare j k s t h12) ≪≫
      Functor.isoWhiskerRight (scalarSquare f g r s h01) (ModuleCat.extendScalars k) ≪≫
      Functor.isoWhiskerLeft (ModuleCat.extendScalars r)
        (ModuleCat.extendScalarsComp.{u, u} g k).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext P
  apply scalarTriple_hom_ext.{u, u} f j t
  intro x
  simp -implicitDefEqProofs only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Iso.symm_hom, ModuleCat.comp_apply]
  erw [ModuleCat.ExtendScalars.map_tmul t
    ((ModuleCat.extendScalarsComp.{u, u} f j).inv.app P)
    1 ((1 : T) ⊗ₜ[S, j] ((1 : S) ⊗ₜ[R, f] x))]
  erw [scalarComp_inv_tmul.{u, u} f j P 1 1 x]
  simp -implicitDefEqProofs only [map_one, mul_one]
  erw [scalarSquare_one (j.comp f) (k.comp g) r t h02 P x]
  erw [scalarSquare_one j k s t h12 ((ModuleCat.extendScalars f).obj P)
    ((1 : S) ⊗ₜ[R, f] x)]
  erw [ModuleCat.ExtendScalars.map_tmul k ((scalarSquare f g r s h01).hom.app P)
    1 ((1 : S') ⊗ₜ[S, s] ((1 : S) ⊗ₜ[R, f] x))]
  erw [scalarSquare_one f g r s h01 P x]
  erw [scalarComp_inv_tmul.{u, u} g k ((ModuleCat.extendScalars r).obj P)
    1 1 ((1 : R') ⊗ₜ[R, r] x)]
  simp -implicitDefEqProofs only [map_one, mul_one]

private theorem fieldTower_eq {K L M : Type u} [Field K] [Field L] [Field M]
    (f : K →+* L) (g : L →+* M) :
    DerivedCategory.fieldScalarTower f g =
      (Functor.mapDerivedCategoryCompIso (ModuleCat.extendScalars.{u, u, u} f)
        (ModuleCat.extendScalars.{u, u, u} g)).symm ≪≫
        Functor.mapDerivedCategoryNatIso (ModuleCat.extendScalarsComp.{u, u} f g).symm := by
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} K) (.up ℤ))
  intro P
  apply (cancel_mono
    ((ModuleCat.extendScalars.{u, u, u} (g.comp f)).mapDerivedCategoryFactors.hom.app P)).mp
  simp -implicitDefEqProofs only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Category.assoc]
  erw [DerivedCategory.tower_fac, Functor.mapDerivedCategoryNatIso_fac]
  have hc := Functor.mapDerivedCategoryCompIso_hom_app_factors
    (ModuleCat.extendScalars.{u, u, u} f) (ModuleCat.extendScalars.{u, u, u} g) P
  have hc' := congrArg
    (fun z ↦ (Functor.mapDerivedCategoryCompIso (ModuleCat.extendScalars.{u, u, u} f)
      (ModuleCat.extendScalars.{u, u, u} g)).inv.app (DerivedCategory.Q.obj P) ≫ z) hc
  simp -implicitDefEqProofs only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] at hc'
  simp -implicitDefEqProofs only [← Category.assoc]
  erw [hc']
  rfl

private theorem derived_eqToIso {K L : Type u} [Field K] [Field L]
    (f g : K →+* L) (h : f = g) :
    Functor.mapDerivedCategoryNatIso
        (eqToIso (congrArg (ModuleCat.extendScalars.{u, u, u}) h)) =
      eqToIso (congrArg DerivedCategory.fieldDerivedScalarExtension h) := by
  subst g
  apply Iso.ext
  exact Functor.mapDerivedCategoryNatIso_refl

private noncomputable def derivedSquare
    {R S R' S' : Type u} [Field R] [Field S] [Field R'] [Field S']
    (f : R →+* S) (g : R' →+* S') (r : R →+* R') (s : S →+* S')
    (h : s.comp f = g.comp r) :
    DerivedCategory.fieldDerivedScalarExtension f ⋙
        DerivedCategory.fieldDerivedScalarExtension s ≅
      DerivedCategory.fieldDerivedScalarExtension r ⋙
        DerivedCategory.fieldDerivedScalarExtension g :=
  DerivedCategory.fieldScalarTower f s ≪≫
    eqToIso (congrArg DerivedCategory.fieldDerivedScalarExtension h) ≪≫
    (DerivedCategory.fieldScalarTower r g).symm

private theorem scalarSquare_derived
    {R S R' S' : Type u} [Field R] [Field S] [Field R'] [Field S']
    (f : R →+* S) (g : R' →+* S') (r : R →+* R') (s : S →+* S')
    (h : s.comp f = g.comp r) :
    Functor.mapDerivedCategorySquareIso (scalarSquare f g r s h) =
      derivedSquare f g r s h := by
  apply Iso.ext
  simp -implicitDefEqProofs only [Functor.mapDerivedCategorySquareIso, scalarSquare, derivedSquare,
    fieldTower_eq, Functor.mapDerivedCategoryNatIso_trans,
    Functor.mapDerivedCategoryNatIso_symm,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc]
  have he := derived_eqToIso (s.comp f) (g.comp r) h
  have hs : Functor.mapDerivedCategoryNatIso (ModuleCat.extendScalarsComp.{u, u} r g).symm =
      (Functor.mapDerivedCategoryNatIso (ModuleCat.extendScalarsComp.{u, u} r g)).symm :=
    Iso.ext (Functor.mapDerivedCategoryNatIso_symm _)
  erw [he, hs]
  rfl

private theorem derivedSquare_tower
    {R S T R' S' T' : Type u}
    [Field R] [Field S] [Field T] [Field R'] [Field S'] [Field T']
    (f : R →+* S) (j : S →+* T) (g : R' →+* S') (k : S' →+* T')
    (r : R →+* R') (s : S →+* S') (t : T →+* T')
    (h01 : s.comp f = g.comp r) (h12 : t.comp j = k.comp s)
    (h02 : t.comp (j.comp f) = (k.comp g).comp r)
    (K : DerivedCategory (ModuleCat.{u} R)) :
    (DerivedCategory.fieldDerivedScalarExtension t).map
      ((DerivedCategory.fieldScalarTower f j).hom.app K) ≫
      (derivedSquare (j.comp f) (k.comp g) r t h02).hom.app K =
    (derivedSquare j k s t h12).hom.app
        ((DerivedCategory.fieldDerivedScalarExtension f).obj K) ≫
      (DerivedCategory.fieldDerivedScalarExtension k).map
        ((derivedSquare f g r s h01).hom.app K) ≫
      (DerivedCategory.fieldScalarTower g k).hom.app
        ((DerivedCategory.fieldDerivedScalarExtension r).obj K) := by
  erw [fieldTower_eq, fieldTower_eq]
  simp -implicitDefEqProofs only [← scalarSquare_derived]
  exact deriveCoefficientTower
    (ModuleCat.extendScalars.{u, u, u} f) (ModuleCat.extendScalars j)
    (ModuleCat.extendScalars t) (ModuleCat.extendScalars r) (ModuleCat.extendScalars s)
    (ModuleCat.extendScalars g) (ModuleCat.extendScalars k)
    (ModuleCat.extendScalars (j.comp f)) (ModuleCat.extendScalars (k.comp g))
    (ModuleCat.extendScalarsComp.{u, u} f j).symm
    (scalarSquare (j.comp f) (k.comp g) r t h02) (scalarSquare j k s t h12)
    (scalarSquare f g r s h01) (ModuleCat.extendScalarsComp.{u, u} g k).symm
    (scalarSquare_tower f j g k r s t h01 h12 h02) K

private theorem tensorLift_ordinary_tower :
    Functor.isoWhiskerRight (ModuleCat.extendScalarsComp.{u, u}
        ι.toRingHom κ.toRingHom).symm (ModuleCat.uliftFunctor.{u + 1, u} M) ≪≫
        (pointFibreTensorLift_existsUnique l E M (κ.comp ι)).exists.choose =
      Functor.isoWhiskerLeft (ModuleCat.extendScalars.{u, u, u} ι.toRingHom)
          (pointFibreTensorLift_existsUnique l L M κ).exists.choose ≪≫
        Functor.isoWhiskerRight (pointFibreTensorLift_existsUnique l E L ι).exists.choose
          (ModuleCat.extendScalars.{u, u, u + 1} κ.toRingHom) ≪≫
        Functor.isoWhiskerLeft (ModuleCat.uliftFunctor.{u + 1, u} E)
          (ModuleCat.extendScalarsComp.{u, u + 1} ι.toRingHom κ.toRingHom).symm := by
  let := ι.toRingHom.toAlgebra
  let := κ.toRingHom.toAlgebra
  let := (κ.comp ι).toRingHom.toAlgebra
  apply Iso.ext
  apply NatTrans.ext
  funext P
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  obtain ⟨z⟩ := z
  let a := ((pointFibreTensorLift_existsUnique l E M (κ.comp ι)).exists.choose.hom.app P).hom.comp
    ((ULift.moduleEquiv (R := M)).symm.toLinearMap.comp
      ((ModuleCat.extendScalarsComp.{u, u} ι.toRingHom κ.toRingHom).inv.app P).hom)
  let b := (((Functor.isoWhiskerLeft (ModuleCat.extendScalars.{u, u, u} ι.toRingHom)
      (pointFibreTensorLift_existsUnique l L M κ).exists.choose ≪≫
      Functor.isoWhiskerRight (pointFibreTensorLift_existsUnique l E L ι).exists.choose
        (ModuleCat.extendScalars.{u, u, u + 1} κ.toRingHom) ≪≫
      Functor.isoWhiskerLeft (ModuleCat.uliftFunctor.{u + 1, u} E)
        (ModuleCat.extendScalarsComp.{u, u + 1} ι.toRingHom κ.toRingHom).symm).hom.app P).hom).comp
          (ULift.moduleEquiv (R := M)).symm.toLinearMap
  change a z = b z
  induction z using TensorProduct.induction_on with
  | zero =>
      simp -implicitDefEqProofs only [map_zero]
      with_unfolding_all rfl
  | add z w hz hw =>
      simp -implicitDefEqProofs only [map_add, hz, hw]
      with_unfolding_all rfl
  | tmul c y =>
      induction y using TensorProduct.induction_on with
      | zero =>
          simp -implicitDefEqProofs only [TensorProduct.tmul_zero, map_zero]
          with_unfolding_all rfl
      | add y z hy hz =>
          simp -implicitDefEqProofs only [TensorProduct.tmul_add, map_add, hy, hz]
          with_unfolding_all rfl
      | tmul b x =>
          change (pointFibreTensorLift_existsUnique l E M (κ.comp ι)).exists.choose.hom.app P
            (ULift.up ((ModuleCat.extendScalarsComp.{u, u}
              ι.toRingHom κ.toRingHom).inv.app P
                (c ⊗ₜ[L, κ.toRingHom] (b ⊗ₜ[E, ι.toRingHom] x)))) = _
          erw [scalarComp_inv_tmul.{u, u}]
          erw [(pointFibreTensorLift_existsUnique l E M (κ.comp ι)).exists.choose_spec]
          change _ = (ModuleCat.extendScalarsComp.{u, u + 1} ι.toRingHom κ.toRingHom).inv.app
            ((ModuleCat.uliftFunctor.{u + 1, u} E).obj P)
              ((ModuleCat.extendScalars κ.toRingHom).map
                ((pointFibreTensorLift_existsUnique l E L ι).exists.choose.hom.app P)
                  ((pointFibreTensorLift_existsUnique l L M κ).exists.choose.hom.app
                    ((ModuleCat.extendScalars ι.toRingHom).obj P)
                      (ULift.up (c ⊗ₜ[L, κ.toRingHom] (b ⊗ₜ[E, ι.toRingHom] x)))))
          erw [(pointFibreTensorLift_existsUnique l L M κ).exists.choose_spec,
            ModuleCat.ExtendScalars.map_tmul,
            (pointFibreTensorLift_existsUnique l E L ι).exists.choose_spec,
            scalarComp_inv_tmul.{u, u + 1}]
          with_unfolding_all rfl

private theorem tensorLift_derived_tower (K : DerivedCategory (ModuleCat.{u} E)) :
    (ModuleCat.uliftFunctor.{u + 1, u} M).mapDerivedCategory.map
      ((DerivedCategory.fieldScalarTower ι.toRingHom κ.toRingHom).hom.app K) ≫
      (pointFibreTensorLiftIso l E M (κ.comp ι)).hom.app K =
    (pointFibreTensorLiftIso l L M κ).hom.app
      ((DerivedCategory.fieldDerivedScalarExtension ι.toRingHom).obj K) ≫
      (pointCoefficientFieldDerivedTensor l L M κ).map
        ((pointFibreTensorLiftIso l E L ι).hom.app K) ≫
      (pointCoefficientFieldDerivedAssoc l E L ι M κ).hom.app
        ((ModuleCat.uliftFunctor.{u + 1, u} E).mapDerivedCategory.obj K) := by
  erw [fieldTower_eq]
  exact deriveCoefficientTower
    (ModuleCat.extendScalars.{u, u, u} ι.toRingHom)
    (ModuleCat.extendScalars.{u, u, u} κ.toRingHom)
    (ModuleCat.uliftFunctor.{u + 1, u} M)
    (ModuleCat.uliftFunctor.{u + 1, u} E)
    (ModuleCat.uliftFunctor.{u + 1, u} L)
    (ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom)
    (ModuleCat.extendScalars.{u, u, u + 1} κ.toRingHom)
    (ModuleCat.extendScalars.{u, u, u} (κ.comp ι).toRingHom)
    (ModuleCat.extendScalars.{u, u, u + 1} (κ.comp ι).toRingHom)
    (ModuleCat.extendScalarsComp.{u, u} ι.toRingHom κ.toRingHom).symm
    (pointFibreTensorLift_existsUnique l E M (κ.comp ι)).exists.choose
    (pointFibreTensorLift_existsUnique l L M κ).exists.choose
    (pointFibreTensorLift_existsUnique l E L ι).exists.choose
    (ModuleCat.extendScalarsComp.{u, u + 1} ι.toRingHom κ.toRingHom).symm
    (tensorLift_ordinary_tower l E L M ι κ) K

private theorem pointAssociator_eq :
    (CompletedLineTensor.associatorData l E (Spec (.of k)) L ι M κ).derived =
      pointDerivedTensorAssoc k l E L ι M κ := by
  have hd : (pointOrdinaryTensorAssoc k l E L ι M κ,
      pointDerivedTensorAssoc k l E L ι M κ) =
      CompletedLineTensor.associatorData l E (Spec (.of k)) L ι M κ := by
    apply (CompletedLineTensor.associatorData_existsUnique
      l E (Spec (.of k)) L ι M κ).unique
    · refine ⟨(pointOrdinaryTensorAssoc_existsUnique k l E L ι M κ).exists.choose_spec, ?_⟩
      intro P
      let F := completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k))
      let G := completedOrdinaryScalarExtension.{u, u} l L M κ (Spec (.of k))
      let J := completedOrdinaryScalarExtension.{u, u} l E M (κ.comp ι) (Spec (.of k))
      have hF := (pointOrdinaryDerivedComparison_existsUnique k l E L ι).exists.choose_spec
      change ∀ P : CochainComplex (integralTowerModules l E (Spec (.of k))) ℤ,
        (pointOrdinaryDerivedComparison k l E L ι).hom.app (DerivedCategory.Q.obj P) ≫
          (completedOrdinaryScalarExtension l E L ι
            (Spec (.of k))).mapDerivedCategoryFactors.hom.app P = _ at hF
      have hG := (pointOrdinaryDerivedComparison_existsUnique k l L M κ).exists.choose_spec
      change ∀ P : CochainComplex (integralTowerModules l L (Spec (.of k))) ℤ,
        (pointOrdinaryDerivedComparison k l L M κ).hom.app (DerivedCategory.Q.obj P) ≫
          (completedOrdinaryScalarExtension l L M κ
            (Spec (.of k))).mapDerivedCategoryFactors.hom.app P = _ at hG
      have hJ := (pointOrdinaryDerivedComparison_existsUnique
        k l E M (κ.comp ι)).exists.choose_spec
      change ∀ P : CochainComplex (integralTowerModules l E (Spec (.of k))) ℤ,
        (pointOrdinaryDerivedComparison k l E M (κ.comp ι)).hom.app (DerivedCategory.Q.obj P) ≫
          (completedOrdinaryScalarExtension l E M (κ.comp ι)
            (Spec (.of k))).mapDerivedCategoryFactors.hom.app P = _ at hJ
      change _ = (pointDerivedTensorAssoc k l E L ι M κ).hom.app _ ≫ _
      erw [← hJ P.obj]
      simp -implicitDefEqProofs only [pointDerivedTensorAssoc, Iso.trans_hom, Iso.symm_hom,
        NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
        Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.assoc,
        Iso.inv_hom_id_app_assoc, CompletedLineTensor.AssociatorData.sheaf,
        CompletedLineTensor.scalarAssociatorComplex]
      erw [Functor.mapDerivedCategoryNatIso_fac]
      have hc := Functor.mapDerivedCategoryCompIso_hom_app_factors F G P.obj
      erw [← reassoc_of% hc]
      simp -implicitDefEqProofs only [F, G, Iso.inv_hom_id_app_assoc]
      erw [← (pointOrdinaryDerivedComparison k l L M κ).hom.naturality_assoc
        (F.mapDerivedCategoryFactors.hom.app P.obj)]
      erw [← Functor.map_comp_assoc, hF P.obj]
      erw [reassoc_of% (hG ((F.mapHomologicalComplex (.up ℤ)).obj P.obj))]
      rfl
    · exact (CompletedLineTensor.associatorData_existsUnique
        l E (Spec (.of k)) L ι M κ).exists.choose_spec
  exact (congrArg CompletedLineTensor.AssociatorData.derived hd).symm

private theorem integralComparison_hom (X : Scheme.{u})
    (K : sfIntegralConstructibleCategory l E X) :
    (sfIntegralOrdinaryComparison l E L ι X).hom.app K =
      (scalarCompletion l E L ι X).app K.obj := by
  let χ := scalarCompletion l E L ι X
  have hχ := (scalarCompletion_existsUnique l E L ι X).exists.choose_spec
  have (N : sfIntegralConstructibleCategory l E X) : IsIso (χ.app N.obj) :=
    hχ.2 N.obj N.property.1
  let c : (sfIntegralConstructible l E X).ι ⋙ integralOrdinaryDerivedScalar l E L ι X ≅
      (sfIntegralConstructible l E X).ι ⋙ integralScalarExtension l E L ι X :=
    NatIso.ofComponents (fun N ↦ asIso (χ.app N.obj)) (fun f ↦ χ.naturality f.hom)
  have hc : c = sfIntegralOrdinaryComparison l E L ι X :=
    (sfIntegralOrdinaryComparison_existsUnique l E L ι X).unique
      (fun P _ ↦ hχ.1 P)
      (sfIntegralOrdinaryComparison_existsUnique l E L ι X).exists.choose_spec
  exact (congrArg (fun e ↦ e.hom.app K) hc).symm

private theorem integralAssociator_eq
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (K : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :
    ((sfIntegralScalarComp l E L ι (Spec (.of D.k)) 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) M κ).hom.app K).hom =
    (pointIntegralScalarAssoc l E L ι M κ D hl K.obj
      ((pointIntegralConstructible_iff l E D hl K.obj).mpr K.property)).hom := by
  let X := Spec (.of D.k)
  let TEL := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X
  let OEL := integralOrdinaryDerivedScalar l E L ι X
  let OLM := integralOrdinaryDerivedScalar l L M κ X
  let CLM := completedDerivedScalarExtension.{u, u} l L M κ X
  let cEL := (sfIntegralOrdinaryComparison l E L ι X).app K
  let cLM := (sfIntegralOrdinaryComparison l L M κ X).app (TEL.obj K)
  let cEM := (sfIntegralOrdinaryComparison l E M (κ.comp ι) X).app K
  let χEL := pointConstructibleCompletionIso l E L ι D hl K.obj
    ((pointIntegralConstructible_iff l E D hl K.obj).mpr K.property)
  let χLM := pointConstructibleCompletionIso l L M κ D hl (TEL.obj K).obj
    ((pointIntegralConstructible_iff l L D hl (TEL.obj K).obj).mpr (TEL.obj K).property)
  let χEM := pointConstructibleCompletionIso l E M (κ.comp ι) D hl K.obj
    ((pointIntegralConstructible_iff l E D hl K.obj).mpr K.property)
  obtain ⟨eEL, eLM, eEM, hEL, hLM, hEM, ha⟩ :=
    (integralScalarOrdinaryModelCoherence l).2 E L M ι κ X
  have hEL' : eEL.hom.app K.obj ≫ χEL.hom = cEL.hom := by
    simpa -implicitDefEqProofs only [cEL, χEL, Iso.app_hom, integralComparison_hom,
      pointConstructibleCompletionIso, asIso_hom, NatTrans.comp_app] using
      NatTrans.congr_app hEL K.obj
  have hLM' : eLM.hom.app (TEL.obj K).obj ≫ χLM.hom = cLM.hom := by
    simpa -implicitDefEqProofs only [cLM, χLM, Iso.app_hom, integralComparison_hom,
      pointConstructibleCompletionIso, asIso_hom, NatTrans.comp_app] using
      NatTrans.congr_app hLM (TEL.obj K).obj
  have hEM' : eEM.hom.app K.obj ≫ χEM.hom = cEM.hom := by
    simpa -implicitDefEqProofs only [cEM, χEM, Iso.app_hom, integralComparison_hom,
      pointConstructibleCompletionIso, asIso_hom, NatTrans.comp_app] using
      NatTrans.congr_app hEM K.obj
  have hp : eLM.hom.app (OEL.obj K.obj) ≫ CLM.map (eEL.hom.app K.obj) ≫
      CLM.map χEL.hom ≫ χLM.hom = OLM.map cEL.hom ≫ cLM.hom := by
    erw [← Functor.map_comp_assoc, hEL', ← eLM.hom.naturality_assoc]
    erw [hLM']
  have ha' : eLM.hom.app (OEL.obj K.obj) ≫ CLM.map (eEL.hom.app K.obj) ≫
      (pointDerivedTensorAssoc D.k l E L ι M κ).hom.app K.obj =
      (integralOrdinaryDerivedScalarComp l E L ι X M κ).hom.app K.obj ≫
        eEM.hom.app K.obj := by
    have hh := congrArg (fun e ↦ e.hom.app K.obj) ha
    simpa -implicitDefEqProofs only [X, pointAssociator_eq, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app] using hh
  apply (cancel_epi cLM.hom).mp
  apply (cancel_epi (OLM.map cEL.hom)).mp
  erw [(sfIntegralScalarComp_existsUnique l E L ι X 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) M κ).exists.choose_spec K]
  change OLM.map cEL.hom ≫ cLM.hom ≫
    (cLM.inv ≫ OLM.map cEL.inv ≫ _ ≫ cEM.hom) = _
  simp -implicitDefEqProofs only [Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  change _ = OLM.map cEL.hom ≫ cLM.hom ≫
    (χLM.inv ≫ CLM.map χEL.inv ≫
      (pointDerivedTensorAssoc D.k l E L ι M κ).hom.app K.obj ≫ χEM.hom)
  erw [← reassoc_of% hp]
  simp -implicitDefEqProofs only [Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [reassoc_of% ha', hEM']

private theorem fdScalar_obj {E L : Type u} [Field E] [Field L]
    (f : E →+* L) (X : (DerivedCategory.pointFiniteDimensional E).FullSubcategory) :
    ((DerivedCategory.pointFdScalarExtension f).obj X).obj =
      (DerivedCategory.fieldDerivedScalarExtension f).obj X.obj := rfl

private theorem fdScalar_map {E L : Type u} [Field E] [Field L]
    (f : E →+* L) {X Y : (DerivedCategory.pointFiniteDimensional E).FullSubcategory}
    (g : X ⟶ Y) :
    ((DerivedCategory.pointFdScalarExtension f).map g).hom =
      (DerivedCategory.fieldDerivedScalarExtension f).map g.hom := rfl

private theorem fdTower_hom {E L M : Type u} [Field E] [Field L] [Field M]
    (f : E →+* L) (g : L →+* M)
    (X : (DerivedCategory.pointFiniteDimensional E).FullSubcategory) :
    ((pointFibreFdTensorTower f g).hom.app X).hom =
      (DerivedCategory.fieldScalarTower f g).hom.app X.obj := by
  have h := ((DerivedCategory.pointFiniteDimensional M).fullyFaithfulι.whiskeringRight
    ((DerivedCategory.pointFiniteDimensional E).FullSubcategory)).map_preimage
      (X := DerivedCategory.pointFdScalarExtension f ⋙
        DerivedCategory.pointFdScalarExtension g)
      (Y := DerivedCategory.pointFdScalarExtension (g.comp f))
      (Functor.isoWhiskerLeft (DerivedCategory.pointFiniteDimensional E).ι
        (DerivedCategory.fieldScalarTower f g)).hom
  simpa -implicitDefEqProofs only [pointFibreFdTensorTower, Functor.FullyFaithful.preimageIso,
    Functor.whiskeringRight_obj_map, Functor.whiskeringRight_obj_obj,
    Functor.comp_obj, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    ObjectProperty.ι_map, ObjectProperty.ι_obj] using
    congrArg (fun t ↦ t.app X) h

private theorem carrierTensorTower
    (X : (DerivedCategory.pointFiniteDimensional E).FullSubcategory) :
    (pointFdCarrierLift M).map
        ((pointFibreFdTensorTower ι.toRingHom κ.toRingHom).hom.app X) ≫
      (pointFibreTensorLiftIso l E M (κ.comp ι)).hom.app X.obj =
    (pointFibreTensorLiftIso l L M κ).hom.app
        ((DerivedCategory.pointFdScalarExtension ι.toRingHom).obj X).obj ≫
      (pointCoefficientFieldDerivedTensor l L M κ).map
        ((pointFibreTensorLiftIso l E L ι).hom.app X.obj) ≫
      (pointCoefficientFieldDerivedAssoc l E L ι M κ).hom.app
        ((pointFdCarrierLift E).obj X) := by
  have he := eq_of_heq (appHEq (pointFibreTensorLiftIso l L M κ).hom
    (fdScalar_obj ι.toRingHom X))
  erw [he]
  simp -implicitDefEqProofs only [pointFdCarrierLift, Functor.comp_map, Functor.comp_obj,
    ObjectProperty.ι_map, ObjectProperty.ι_obj, fdTower_hom]
  exact tensorLift_derived_tower l E L M ι κ X.obj

private theorem algTensorTower_refl :
    (pointFibreFdTensorTower ι.toRingHom κ.toRingHom ≪≫
      eqToIso (congrArg DerivedCategory.pointFdScalarExtension
        (congrArg AlgHom.toRingHom (rfl : κ.comp ι = κ.comp ι)))) =
      pointFibreFdTensorTower ι.toRingHom κ.toRingHom := by
  change pointFibreFdTensorTower ι.toRingHom κ.toRingHom ≪≫
    Iso.refl _ = pointFibreFdTensorTower ι.toRingHom κ.toRingHom
  exact Iso.trans_refl _

private theorem rationalCarrier_formula
    (K : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :
    (pointFdCarrierLift L).map
      ((pointRationalFibreScalarIso D l hl E L ι).hom.app
        ((sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj K)) =
      (pointRationalScalarIntegralLargeIso D l hl E L ι).hom.app K := by
  let Q := sfRationalConstructibleLocalization l E (Spec (.of D.k))
  let V := pointCoefficientFieldDerivedTensor l E L ι
  let t := (pointFibreTensorLiftIso l E L ι).hom.app
    ((pointRationalFibre D l hl E).obj (Q.obj K)).obj ≫
      V.map (pointRationalNormalization D l hl E (Q.obj K)).hom
  apply (cancel_mono t).mp
  have h := (pointRationalFibreScalar_existsUnique D l hl E L ι).exists.choose_spec K
  apply eq_of_heq
  apply h.trans
  symm
  change HEq ((pointRationalScalarIntegralLargeIso D l hl E L ι).hom.app K ≫
      (pointFibreTensorLiftIso l E L ι).hom.app
        ((pointRationalFibre D l hl E).obj (Q.obj K)).obj ≫
      V.map (pointRationalNormalization D l hl E (Q.obj K)).hom) _
  dsimp only [V, Q]
  erw [← pointRationalNormalizationIso_hom_app D l hl E K]
  simp -implicitDefEqProofs only [pointRationalScalarIntegralLargeIso, Iso.trans_hom,
    NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Iso.symm_hom, Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]
  erw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.comp_id]
  erw [pointRationalNormalizationIso_hom_app]
  simp -implicitDefEqProofs only [pointRationalNormalization, Iso.trans_hom, Functor.mapIso_hom,
    pointIntegralScalarSectionsIso, NatIso.ofComponents_hom_app,
    pointRationalScalarLocalizationIso, pointRationalFibreObjIso, Functor.comp_map]
  repeat' first | erw [eqToIso.hom] | erw [eqToHom_map]
  dsimp only [sfRationalConstructibleLocalization, ScalarLocalization.localization]
  erw [Category.assoc, eqToHom_comp_heq_iff]
  erw [eqToHom_comp_heq_iff]

private theorem rationalCarrier_normalized
    (K : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :
    (pointFdCarrierLift L).map
      ((pointRationalFibreScalarIso D l hl E L ι).hom.app
        ((sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj K)) ≫
      (pointFibreTensorLiftIso l E L ι).hom.app
        ((pointRationalFibre D l hl E).obj
          ((sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj K)).obj ≫
      (pointCoefficientFieldDerivedTensor l E L ι).map
        ((pointRationalNormalizationIso D l hl E).hom.app K) =
    (pointRationalFibre D l hl L ⋙ pointFdCarrierLift L).map
      ((pointRationalScalarLocalizationIso D l E L ι).hom.app K) ≫
      (pointRationalNormalizationIso D l hl L).hom.app
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι (Spec (.of D.k))).obj K) ≫
      (pointIntegralScalarSectionsIso D l hl E L ι).hom.app K := by
  erw [rationalCarrier_formula]
  simp -implicitDefEqProofs only [pointRationalScalarIntegralLargeIso, Iso.trans_hom,
    NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Iso.symm_hom, Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]
  erw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.comp_id]

private theorem carrierLift_faithful (F : Type u) [Field F] :
    (pointFdCarrierLift F).Faithful := by
  let := pointFibreSizeLift_equivalence F
  let I := (DerivedCategory.pointFiniteDimensional F).ι
  let I' := (DerivedCategory.pointFiniteDimensional (ULift.{u + 1, u} F)).ι
  let V := (pointFibreCoefficientDown F).mapDerivedCategory
  let W := pointFibreSizeLift F ⋙ I' ⋙ V
  have : V.IsEquivalence := inferInstance
  have hW : W.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful _
  exact (hW.ofIso (Functor.isoWhiskerLeft I (pointFibreLiftDownIso F))).faithful

private theorem rationalLocalization_tower
    (K : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :
    (sfRationalScalarExtension l L (Spec (.of D.k)) 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) M κ).map
        ((pointRationalScalarLocalizationIso D l E L ι).hom.app K) ≫
      (pointRationalScalarLocalizationIso D l L M κ).hom.app
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι (Spec (.of D.k))).obj K) ≫
      (sfRationalConstructibleLocalization l M (Spec (.of D.k))).map
        ((sfIntegralScalarComp l E L ι (Spec (.of D.k)) 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) M κ).hom.app K) =
    (sfRationalScalarComp l E L ι (Spec (.of D.k)) 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) M κ).hom.app
        ((sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj K) ≫
      (pointRationalScalarLocalizationIso D l E M (κ.comp ι)).hom.app K := by
  let Q := sfRationalConstructibleLocalization l E (Spec (.of D.k))
  let S := sfRationalScalarExtension l L (Spec (.of D.k)) 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) M κ
  let T := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι (Spec (.of D.k))
  have hF := (sfRationalScalarExtension_existsUnique l E (Spec (.of D.k)) 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.1 (Q.obj K)
  have hG := (sfRationalScalarExtension_existsUnique l L (Spec (.of D.k)) 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) M κ).exists.choose_spec.2.1
      ((sfRationalConstructibleLocalization l L (Spec (.of D.k))).obj (T.obj K))
  have hH := (sfRationalScalarExtension_existsUnique l E (Spec (.of D.k)) 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) M (κ.comp ι)).exists.choose_spec.2.1 (Q.obj K)
  have hsrc := (congrArg S.obj hF).trans hG
  have ha := (sfRationalScalarComp_existsUnique l E L ι (Spec (.of D.k)) 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) M κ).exists.choose_spec (Q.obj K)
  have he := (conj_eqToHom_iff_heq _ _ hsrc hH).2 ha
  simp -implicitDefEqProofs only [pointRationalScalarLocalizationIso, NatIso.ofComponents_hom_app]
  repeat' first | erw [eqToIso.hom] | erw [eqToHom_map]
  erw [he]
  simp -implicitDefEqProofs only [Category.assoc]
  dsimp only [Q, sfRationalConstructibleLocalization, ScalarLocalization.localization]
  repeat' first | erw [Category.assoc] | erw [eqToHom_trans_assoc] | erw [eqToHom_trans]
  simp -implicitDefEqProofs only [eqToHom_refl, Category.comp_id]
  with_unfolding_all rfl

private theorem integralSections_tower
    (K : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :
    (pointCompletedDerivedSections D.k l M ⋙ pointModuleDerivedRationalization l M).map
      (((sfIntegralScalarComp l E L ι (Spec (.of D.k)) 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) M κ).hom.app K).hom) ≫
      (pointIntegralScalarSectionsIso D l hl E M (κ.comp ι)).hom.app K =
    (pointIntegralScalarSectionsIso D l hl L M κ).hom.app
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι (Spec (.of D.k))).obj K) ≫
      (pointCoefficientFieldDerivedTensor l L M κ).map
        ((pointIntegralScalarSectionsIso D l hl E L ι).hom.app K) ≫
      (pointCoefficientFieldDerivedAssoc l E L ι M κ).hom.app
        ((pointModuleDerivedRationalization l E).obj
          ((pointCompletedDerivedSections D.k l E).obj K.obj)) := by
  erw [integralAssociator_eq l E L M ι κ D hl K]
  have h := pointRationalSectionsTower l E L ι M κ D hl K.obj
    ((pointIntegralConstructible_iff l E D hl K.obj).mpr K.property)
  simpa -implicitDefEqProofs only [pointIntegralScalarSectionsIso, NatIso.ofComponents_hom_app,
    Functor.comp_map, sfConstructibleIntegralScalarExtension, Functor.comp_obj,
    ObjectProperty.lift, ObjectProperty.ι_obj, Functor.comp_obj] using h

private theorem rationalFibre_tower
    (K : sfRationalConstructibleCategory l E (Spec (.of D.k))) :
    (pointRationalFibre D l hl M).map
      ((sfRationalScalarComp l E L ι (Spec (.of D.k)) 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) M κ).hom.app K) ≫
      (pointRationalFibreScalarIso D l hl E M (κ.comp ι)).hom.app K =
    (pointRationalFibreScalarIso D l hl L M κ).hom.app
        ((sfRationalScalarExtension l E (Spec (.of D.k)) 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj K) ≫
      (DerivedCategory.pointFdScalarExtension κ.toRingHom).map
        ((pointRationalFibreScalarIso D l hl E L ι).hom.app K) ≫
      (pointFibreFdTensorTower ι.toRingHom κ.toRingHom).hom.app
        ((pointRationalFibre D l hl E).obj K) := by
  obtain ⟨K⟩ := K
  let QE := sfRationalConstructibleLocalization l E (Spec (.of D.k))
  let QL := sfRationalConstructibleLocalization l L (Spec (.of D.k))
  let QM := sfRationalConstructibleLocalization l M (Spec (.of D.k))
  let SEL := sfRationalScalarExtension l E (Spec (.of D.k)) 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι
  let SLM := sfRationalScalarExtension l L (Spec (.of D.k)) 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) M κ
  let SEM := sfRationalScalarExtension l E (Spec (.of D.k)) 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) M (κ.comp ι)
  let TEL := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι (Spec (.of D.k))
  let TLM := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L M κ (Spec (.of D.k))
  let TEM := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E M (κ.comp ι) (Spec (.of D.k))
  let RE := pointRationalFibre D l hl E
  let RL := pointRationalFibre D l hl L
  let RM := pointRationalFibre D l hl M
  let UE := pointFdCarrierLift E
  let UL := pointFdCarrierLift L
  let UM := pointFdCarrierLift M
  let F := DerivedCategory.pointFdScalarExtension ι.toRingHom
  let G := DerivedCategory.pointFdScalarExtension κ.toRingHom
  let H := DerivedCategory.pointFdScalarExtension (κ.comp ι).toRingHom
  let V := pointCoefficientFieldDerivedTensor l E L ι
  let W := pointCoefficientFieldDerivedTensor l L M κ
  let J := pointCoefficientFieldDerivedTensor l E M (κ.comp ι)
  let tF : F ⋙ UL ≅ UE ⋙ V := Functor.isoWhiskerLeft
    (DerivedCategory.pointFiniteDimensional E).ι (pointFibreTensorLiftIso l E L ι)
  let tG : G ⋙ UM ≅ UL ⋙ W := Functor.isoWhiskerLeft
    (DerivedCategory.pointFiniteDimensional L).ι (pointFibreTensorLiftIso l L M κ)
  let tH : H ⋙ UM ≅ UE ⋙ J := Functor.isoWhiskerLeft
    (DerivedCategory.pointFiniteDimensional E).ι (pointFibreTensorLiftIso l E M (κ.comp ι))
  let qEL := (pointRationalScalarLocalizationIso D l E L ι).app K
  let qLM := (pointRationalScalarLocalizationIso D l L M κ).app (TEL.obj K)
  let qEM := (pointRationalScalarLocalizationIso D l E M (κ.comp ι)).app K
  let NE := pointRationalNormalizationIso D l hl E
  let NL := pointRationalNormalizationIso D l hl L
  let NM := pointRationalNormalizationIso D l hl M
  let nX := NE.app K
  let nY := (RL ⋙ UL).mapIso qEL ≪≫ NL.app (TEL.obj K)
  let nZ := (RM ⋙ UM).mapIso (SLM.mapIso qEL ≪≫ qLM) ≪≫
    NM.app (TLM.obj (TEL.obj K))
  let nZ' := (RM ⋙ UM).mapIso qEM ≪≫ NM.app (TEM.obj K)
  let aI := sfIntegralScalarComp l E L ι (Spec (.of D.k)) 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) M κ
  let aR := sfRationalScalarComp l E L ι (Spec (.of D.k)) 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) M κ
  let f := (pointRationalFibreScalarIso D l hl E L ι).hom.app (QE.obj K)
  let g := (pointRationalFibreScalarIso D l hl L M κ).hom.app (SEL.obj (QE.obj K))
  let h := (pointRationalFibreScalarIso D l hl E M (κ.comp ι)).hom.app (QE.obj K)
  let r := RM.map (aR.hom.app (QE.obj K))
  let sf := (pointIntegralScalarSectionsIso D l hl E L ι).hom.app K
  let sg := (pointIntegralScalarSectionsIso D l hl L M κ).hom.app (TEL.obj K)
  let sh := (pointIntegralScalarSectionsIso D l hl E M (κ.comp ι)).hom.app K
  let ΓM := (sfIntegralConstructible l M (Spec (.of D.k))).ι ⋙
    pointCompletedDerivedSections D.k l M ⋙ pointModuleDerivedRationalization l M
  let sr := ΓM.map (aI.hom.app K)
  let := carrierLift_faithful M
  apply UM.map_injective
  refine normalizedTower UE UL UM F G H V W J tF tG tH
    (pointFibreFdTensorTower ι.toRingHom κ.toRingHom)
    (pointCoefficientFieldDerivedAssoc l E L ι M κ)
    (RE.obj (QE.obj K)) (RL.obj (SEL.obj (QE.obj K)))
    (RM.obj (SLM.obj (SEL.obj (QE.obj K)))) (RM.obj (SEM.obj (QE.obj K)))
    _ _ _ _ nX nY nZ nZ' f g h r sf sg sh sr ?_ ?_ ?_ ?_ ?_ ?_
  · simpa -implicitDefEqProofs only [f, tF, nX, sf, RE, RL, UL, V, QE, SEL, TEL, qEL, NE, NL, nY,
      Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
      Functor.comp_obj, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      ObjectProperty.ι_obj, Category.assoc] using rationalCarrier_normalized D l hl E L ι K
  · simp -implicitDefEqProofs only [nY, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
      Functor.comp_map]
    have hn := tG.hom.naturality (RL.map qEL.hom)
    dsimp only [Functor.comp_map] at hn
    erw [← reassoc_of% hn]
    have hp := (pointRationalFibreScalarIso D l hl L M κ).hom.naturality qEL.hom
    dsimp only [Functor.comp_map] at hp
    dsimp only [g]
    erw [← Functor.map_comp_assoc, ← hp]
    simp -implicitDefEqProofs only [Functor.map_comp, Category.assoc]
    dsimp only [tG, RM, UM, W, NL]
    erw [rationalCarrier_normalized D l hl L M κ (TEL.obj K)]
    simp -implicitDefEqProofs only [nZ, sg, RM, UM, SLM, qLM, NM, Iso.trans_hom, Functor.mapIso_hom,
      Functor.map_comp, Functor.comp_map, Iso.app_hom, Category.assoc]
    rfl
  · simpa -implicitDefEqProofs only [h, tH, nX, sh, RE, RM, UM, J, QE, SEM, TEM, qEM, NE, NM, nZ',
      Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
      Functor.comp_obj, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      ObjectProperty.ι_obj, Category.assoc] using rationalCarrier_normalized D l hl E M (κ.comp ι) K
  · have hr : (RM ⋙ UM).map (aR.hom.app (QE.obj K)) ≫ (RM ⋙ UM).map qEM.hom ≫
        NM.hom.app (TEM.obj K) =
      (RM ⋙ UM).map (SLM.map qEL.hom ≫ qLM.hom) ≫
        NM.hom.app (TLM.obj (TEL.obj K)) ≫ sr := by
      have hlc := rationalLocalization_tower D l E L ι M κ K
      change SLM.map qEL.hom ≫ qLM.hom ≫ QM.map (aI.hom.app K) =
        aR.hom.app (QE.obj K) ≫ qEM.hom at hlc
      erw [← Functor.map_comp_assoc, ← hlc]
      simp -implicitDefEqProofs only [Functor.map_comp, Functor.comp_map, Category.assoc]
      have hn := NM.hom.naturality (aI.hom.app K)
      change (RM ⋙ UM).map (QM.map (aI.hom.app K)) ≫ NM.hom.app (TEM.obj K) =
        NM.hom.app (TLM.obj (TEL.obj K)) ≫ sr at hn
      simp -implicitDefEqProofs only [Functor.comp_map] at hn
      erw [hn]
    simpa -implicitDefEqProofs only [r, Functor.comp_map, nZ, nZ', Iso.trans_hom,
      Iso.app_hom, Functor.mapIso_hom,
      Functor.map_comp, Category.assoc] using hr
  · simpa -implicitDefEqProofs only [ΓM, sr, aI, sh, sg, sf, W, J, TLM, TEL, TEM,
      Functor.comp_map, Functor.comp_obj, ObjectProperty.ι_map, ObjectProperty.ι_obj] using
      integralSections_tower D l hl E L ι M κ K
  · exact carrierTensorTower l E L M ι κ (RE.obj (QE.obj K))

private theorem rationalFibre_tower_transport
    (μ : E →ₐ[ℚ_[l]] M) (hμ : κ.comp ι = μ)
    (K : sfRationalConstructibleCategory l E (Spec (.of D.k))) :
    (pointRationalFibre D l hl M).map
      ((GeneralAlgebraicallyClosedCoefficients.scalarAssociator l E L M ι κ μ hμ
        (Spec (.of D.k))).hom.app K) ≫
      (pointRationalFibreScalarIso D l hl E M μ).hom.app K =
    (pointRationalFibreScalarIso D l hl L M κ).hom.app
        ((sfRationalScalarExtension l E (Spec (.of D.k)) 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj K) ≫
      (DerivedCategory.pointFdScalarExtension κ.toRingHom).map
        ((pointRationalFibreScalarIso D l hl E L ι).hom.app K) ≫
      (pointFibreFdTensorTower ι.toRingHom κ.toRingHom ≪≫
        eqToIso (congrArg DerivedCategory.pointFdScalarExtension
          (congrArg AlgHom.toRingHom hμ))).hom.app
            ((pointRationalFibre D l hl E).obj K) := by
  subst μ
  have hs : GeneralAlgebraicallyClosedCoefficients.scalarAssociator l E L M ι κ
      (κ.comp ι) rfl (Spec (.of D.k)) =
      sfRationalScalarComp l E L ι (Spec (.of D.k)) 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) M κ := by
    unfold GeneralAlgebraicallyClosedCoefficients.scalarAssociator
    simp -implicitDefEqProofs only [eqToIso_refl, Iso.trans_refl]
  erw [hs, algTensorTower_refl l E L M ι κ]
  exact rationalFibre_tower D l hl E L ι M κ K

private theorem fdTower_inv {E L M : Type u} [Field E] [Field L] [Field M]
    (f : E →+* L) (g : L →+* M)
    (X : (DerivedCategory.pointFiniteDimensional E).FullSubcategory) :
    ((pointFibreFdTensorTower f g).inv.app X).hom =
      (DerivedCategory.fieldScalarTower f g).inv.app X.obj := by
  have h := ((DerivedCategory.pointFiniteDimensional M).fullyFaithfulι.whiskeringRight
    ((DerivedCategory.pointFiniteDimensional E).FullSubcategory)).map_preimage
      (X := DerivedCategory.pointFdScalarExtension (g.comp f))
      (Y := DerivedCategory.pointFdScalarExtension f ⋙
        DerivedCategory.pointFdScalarExtension g)
      (Functor.isoWhiskerLeft (DerivedCategory.pointFiniteDimensional E).ι
        (DerivedCategory.fieldScalarTower f g)).inv
  simpa only [pointFibreFdTensorTower, Functor.FullyFaithful.preimageIso,
    Functor.whiskeringRight_obj_map, Functor.whiskeringRight_obj_obj,
    Functor.comp_obj, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    ObjectProperty.ι_map, ObjectProperty.ι_obj] using
    congrArg (fun t ↦ t.app X) h

private noncomputable def fdSquare
    {R S R' S' : Type u} [Field R] [Field S] [Field R'] [Field S']
    (f : R →+* S) (g : R' →+* S') (r : R →+* R') (s : S →+* S')
    (h : s.comp f = g.comp r) :
    DerivedCategory.pointFdScalarExtension f ⋙ DerivedCategory.pointFdScalarExtension s ≅
      DerivedCategory.pointFdScalarExtension r ⋙ DerivedCategory.pointFdScalarExtension g :=
  pointFibreFdTensorTower f s ≪≫
    eqToIso (congrArg DerivedCategory.pointFdScalarExtension h) ≪≫
    (pointFibreFdTensorTower r g).symm

private theorem fdTransport_hom {E L : Type u} [Field E] [Field L]
    (f g : E →+* L) (h : f = g)
    (X : (DerivedCategory.pointFiniteDimensional E).FullSubcategory) :
    ((eqToIso (congrArg DerivedCategory.pointFdScalarExtension h)).hom.app X).hom =
      (eqToIso (congrArg DerivedCategory.fieldDerivedScalarExtension h)).hom.app X.obj := by
  subst g
  rfl

private theorem fdSquare_eq_iso
    {R S R' S' : Type u} [Field R] [Field S] [Field R'] [Field S']
    (f : R →+* S) (g : R' →+* S') (r : R →+* R') (s : S →+* S')
    (h : s.comp f = g.comp r) :
    fdSquare f g r s h =
      pointFibreFdTensorTower f s ≪≫
        eqToIso (congrArg DerivedCategory.pointFdScalarExtension h) ≪≫
        (pointFibreFdTensorTower r g).symm := by rfl

private theorem derivedSquare_eq_iso
    {R S R' S' : Type u} [Field R] [Field S] [Field R'] [Field S']
    (f : R →+* S) (g : R' →+* S') (r : R →+* R') (s : S →+* S')
    (h : s.comp f = g.comp r) :
    derivedSquare f g r s h =
      DerivedCategory.fieldScalarTower f s ≪≫
        eqToIso (congrArg DerivedCategory.fieldDerivedScalarExtension h) ≪≫
        (DerivedCategory.fieldScalarTower r g).symm := by rfl

private theorem fdSquare_hom
    {R S R' S' : Type u} [Field R] [Field S] [Field R'] [Field S']
    (f : R →+* S) (g : R' →+* S') (r : R →+* R') (s : S →+* S')
    (h : s.comp f = g.comp r)
    (X : (DerivedCategory.pointFiniteDimensional R).FullSubcategory) :
    ((fdSquare f g r s h).hom.app X).hom = (derivedSquare f g r s h).hom.app X.obj := by
  rw [fdSquare_eq_iso, derivedSquare_eq_iso, isoThree, isoThree]
  exact fullSubcategory_comp_three (DerivedCategory.pointFiniteDimensional S')
    ((pointFibreFdTensorTower f s).hom.app X)
    ((eqToIso (congrArg DerivedCategory.pointFdScalarExtension h)).hom.app X)
    ((pointFibreFdTensorTower r g).inv.app X)
    ((DerivedCategory.fieldScalarTower f s).hom.app X.obj)
    ((eqToIso (congrArg DerivedCategory.fieldDerivedScalarExtension h)).hom.app X.obj)
    ((DerivedCategory.fieldScalarTower r g).inv.app X.obj)
    (fdTower_hom f s X) (fdTransport_hom (s.comp f) (g.comp r) h X) (fdTower_inv r g X)

private theorem fdSquareAfterScalar_heq
    {R S T R' S' : Type u}
    [Field R] [Field S] [Field T] [Field R'] [Field S']
    (f : R →+* S) (j : S →+* T) (k : R' →+* S')
    (s : S →+* R') (t : T →+* S') (h : t.comp j = k.comp s)
    (X : (DerivedCategory.pointFiniteDimensional R).FullSubcategory) :
    HEq (((fdSquare j k s t h).hom.app
      ((DerivedCategory.pointFdScalarExtension f).obj X)).hom)
      ((derivedSquare j k s t h).hom.app
        ((DerivedCategory.fieldDerivedScalarExtension f).obj X.obj)) := by
  exact (heq_of_eq (fdSquare_hom j k s t h
    ((DerivedCategory.pointFdScalarExtension f).obj X))).trans
      (appHEq (derivedSquare j k s t h).hom (fdScalar_obj f X))

private theorem fdSquare_tower
    {R S T R' S' T' : Type u}
    [Field R] [Field S] [Field T] [Field R'] [Field S'] [Field T']
    (f : R →+* S) (j : S →+* T) (g : R' →+* S') (k : S' →+* T')
    (r : R →+* R') (s : S →+* S') (t : T →+* T')
    (h01 : s.comp f = g.comp r) (h12 : t.comp j = k.comp s)
    (h02 : t.comp (j.comp f) = (k.comp g).comp r)
    (X : (DerivedCategory.pointFiniteDimensional R).FullSubcategory) :
    (DerivedCategory.pointFdScalarExtension t).map
      ((pointFibreFdTensorTower f j).hom.app X) ≫
      (fdSquare (j.comp f) (k.comp g) r t h02).hom.app X =
    (fdSquare j k s t h12).hom.app
        ((DerivedCategory.pointFdScalarExtension f).obj X) ≫
      (DerivedCategory.pointFdScalarExtension k).map
        ((fdSquare f g r s h01).hom.app X) ≫
      (pointFibreFdTensorTower g k).hom.app
        ((DerivedCategory.pointFdScalarExtension r).obj X) := by
  refine fullSubcategory_two_three (DerivedCategory.pointFiniteDimensional T')
    ((DerivedCategory.pointFdScalarExtension t).map
      ((pointFibreFdTensorTower f j).hom.app X))
    ((fdSquare (j.comp f) (k.comp g) r t h02).hom.app X)
    ((fdSquare j k s t h12).hom.app
      ((DerivedCategory.pointFdScalarExtension f).obj X))
    ((DerivedCategory.pointFdScalarExtension k).map
      ((fdSquare f g r s h01).hom.app X))
    ((pointFibreFdTensorTower g k).hom.app
      ((DerivedCategory.pointFdScalarExtension r).obj X))
    ((DerivedCategory.fieldDerivedScalarExtension t).map
      ((DerivedCategory.fieldScalarTower f j).hom.app X.obj))
    ((derivedSquare (j.comp f) (k.comp g) r t h02).hom.app X.obj)
    ((derivedSquare j k s t h12).hom.app
      ((DerivedCategory.fieldDerivedScalarExtension f).obj X.obj))
    ((DerivedCategory.fieldDerivedScalarExtension k).map
      ((derivedSquare f g r s h01).hom.app X.obj))
    ((DerivedCategory.fieldScalarTower g k).hom.app
      ((DerivedCategory.fieldDerivedScalarExtension r).obj X.obj)) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [fdScalar_map, fdTower_hom]
  · exact fdSquare_hom _ _ _ _ _ _
  · exact eq_of_heq (fdSquareAfterScalar_heq f j k s t h12 X)
  · rw [fdScalar_map, fdSquare_hom]
  · simpa only [fdScalar_obj] using fdTower_hom g k
      ((DerivedCategory.pointFdScalarExtension r).obj X)
  · exact derivedSquare_tower f j g k r s t h01 h12 h02 X.obj

private theorem fdSquare_tower_transport_left
    {R S T R' S' T' : Type u}
    [Field R] [Field S] [Field T] [Field R'] [Field S'] [Field T']
    (f : R →+* S) (j : S →+* T) (m : R →+* T)
    (g : R' →+* S') (k : S' →+* T') (n : R' →+* T')
    (r : R →+* R') (s : S →+* S') (t : T →+* T')
    (hm : j.comp f = m) (hn : k.comp g = n)
    (h01 : s.comp f = g.comp r) (h12 : t.comp j = k.comp s)
    (h02 : t.comp m = n.comp r)
    (X : (DerivedCategory.pointFiniteDimensional R).FullSubcategory) :
    (DerivedCategory.pointFdScalarExtension t).map
      ((pointFibreFdTensorTower f j ≪≫
        eqToIso (congrArg DerivedCategory.pointFdScalarExtension hm)).hom.app X) ≫
      (fdSquare m n r t h02).hom.app X =
    (fdSquare j k s t h12).hom.app
        ((DerivedCategory.pointFdScalarExtension f).obj X) ≫
      (DerivedCategory.pointFdScalarExtension k).map
        ((fdSquare f g r s h01).hom.app X) ≫
      (pointFibreFdTensorTower g k ≪≫
        eqToIso (congrArg DerivedCategory.pointFdScalarExtension hn)).hom.app
        ((DerivedCategory.pointFdScalarExtension r).obj X) := by
  subst m
  subst n
  simpa only [Iso.trans_hom, NatTrans.comp_app, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Category.comp_id] using
    fdSquare_tower f j g k r s t h01 h12 h02 X

private noncomputable def actualFdTower
    (F G H : AlgebraicallyClosedCoefficients.Index l Ω) (hFG : F ≤ G) (hGH : G ≤ H) :
    DerivedCategory.pointFdScalarExtension (IntermediateField.inclusion hFG).toRingHom ⋙
        DerivedCategory.pointFdScalarExtension (IntermediateField.inclusion hGH).toRingHom ≅
      DerivedCategory.pointFdScalarExtension
        (IntermediateField.inclusion (hFG.trans hGH)).toRingHom :=
  pointFibreFdTensorTower (IntermediateField.inclusion hFG).toRingHom
    (IntermediateField.inclusion hGH).toRingHom ≪≫
      eqToIso (congrArg DerivedCategory.pointFdScalarExtension
        (show (IntermediateField.inclusion hGH).toRingHom.comp
            (IntermediateField.inclusion hFG).toRingHom =
          (IntermediateField.inclusion (hFG.trans hGH)).toRingHom from rfl))

private theorem actualFdTower_eq
    (F G H : AlgebraicallyClosedCoefficients.Index l Ω) (hFG : F ≤ G) (hGH : G ≤ H) :
    actualFdTower l Ω F G H hFG hGH =
      pointFibreFdTensorTower (IntermediateField.inclusion hFG).toRingHom
        (IntermediateField.inclusion hGH).toRingHom := by
  unfold actualFdTower
  change pointFibreFdTensorTower _ _ ≪≫ Iso.refl _ = pointFibreFdTensorTower _ _
  exact Iso.trans_refl _

private theorem stageTransition_spec
    (F G : AlgebraicallyClosedCoefficients.Index l Ω) (h : F ≤ G) :
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (Spec (.of D.k))).T h =
      sfRationalScalarExtension l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) (Spec (.of D.k)) 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime))
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω G)
        (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω F G h) := by
  exact ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
    l Ω (Spec (.of D.k))).exists.choose_spec.1 F G h).trans (by rfl)

private noncomputable def smallStageComparison
    (F G : AlgebraicallyClosedCoefficients.Index l Ω) (h : F ≤ G) :
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (Spec (.of D.k))).T h ⋙
      pointRationalFibre D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω G) ≅
    pointRationalFibre D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) ⋙
      DerivedCategory.pointFdScalarExtension
        (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω F G h).toRingHom :=
  Functor.isoWhiskerRight
    (eqToIso (stageTransition_spec D l Ω F G h)) _ ≪≫
    pointRationalFibreScalarIso D l hl _ _
      (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω F G h)

private theorem smallStageComparison_eq
    (F G : AlgebraicallyClosedCoefficients.Index l Ω) (h : F ≤ G) :
    smallStageComparison D l hl Ω F G h =
      Functor.isoWhiskerRight
        (eqToIso (stageTransition_spec D l Ω F G h)) _ ≪≫
        pointRationalFibreScalarIso D l hl _ _
          (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω F G h) := by rfl

private theorem smallStageAssociator_heq
    (F G H : AlgebraicallyClosedCoefficients.Index l Ω) (hFG : F ≤ G) (hGH : G ≤ H) :
    HEq ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (Spec (.of D.k))).assoc
      hFG hGH)
      (GeneralAlgebraicallyClosedCoefficients.scalarAssociator l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω G)
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω H)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω F G hFG)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω G H hGH)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω F H (hFG.trans hGH))
        ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2 F G H hFG hGH)
        (Spec (.of D.k))) := by
  exact ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
    l Ω (Spec (.of D.k))).exists.choose_spec.2 F G H hFG hGH).trans
      ((GeneralAlgebraicallyClosedCoefficients.associator_existsUnique
        l Ω (Spec (.of D.k)) F G H hFG hGH).exists.choose_spec)

-- Copy the metadata of already elaborated functors rather than synthesizing it again.
-- On Shrink fields, equivalent semiring projections otherwise trigger large kernel reductions.
-- These elaborators emit existing expression subterms; towerHEqAll checks the transports.

private theorem smallStageComparison_heq
    (F G : AlgebraicallyClosedCoefficients.Index l Ω) (h : F ≤ G) :
    HEq (smallStageComparison D l hl Ω F G h)
      (pointRationalFibreScalarIso D l hl
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω G)
        (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω F G h)) := by
  exact (heq_of_eq (smallStageComparison_eq D l hl Ω F G h)).trans
    (whiskerRight_transport_heq (stageTransition_spec D l Ω F G h) _ _
      (pointRationalFibreScalarIso D l hl
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω G)
        (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω F G h)))

private theorem smallStage_tower
    (F G H : AlgebraicallyClosedCoefficients.Index l Ω) (hFG : F ≤ G) (hGH : G ≤ H)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω (Spec (.of D.k)) F) :
    (@CategoryTheory.Functor.map
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω (Spec (.of D.k)) H)
      (GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω (Spec (.of D.k)) H)
      (DerivedCategory.pointFiniteDimensional
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω H)).FullSubcategory
      (nativeTargetCategory% (pointRationalFibre D l hl
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω H)))
      (pointRationalFibre D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω H)) _ _)
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (Spec (.of D.k))).assoc
          hFG hGH).hom.app K) ≫
      (smallStageComparison D l hl Ω F H (hFG.trans hGH)).hom.app K =
    (smallStageComparison D l hl Ω G H hGH).hom.app
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (Spec (.of D.k))).T hFG).obj K) ≫
      (DerivedCategory.pointFdScalarExtension
        (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω G H hGH).toRingHom).map
        ((smallStageComparison D l hl Ω F G hFG).hom.app K) ≫
      (pointFibreFdTensorTower
          (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω F G hFG).toRingHom
          (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω G H hGH).toRingHom ≪≫
        eqToIso (congrArg DerivedCategory.pointFdScalarExtension
          (congrArg AlgHom.toRingHom
            ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2
              F G H hFG hGH)))).hom.app
        ((@CategoryTheory.Functor.obj
          (GeneralAlgebraicallyClosedCoefficients.Stage l Ω (Spec (.of D.k)) F)
          (GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω (Spec (.of D.k)) F)
          (DerivedCategory.pointFiniteDimensional
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)).FullSubcategory
          (nativeTargetCategory% (pointRationalFibre D l hl
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)))
          (pointRationalFibre D l hl
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F))) K) := by
  let EF := AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F
  let EG := AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω G
  let EH := AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω H
  let i := AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω F G hFG
  let j := AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω G H hGH
  let m := AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω F H (hFG.trans hGH)
  let hm := (AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2 F G H hFG hGH
  let S := GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (Spec (.of D.k))
  let h₁ := stageTransition_spec D l Ω F G hFG
  let h₂ := stageTransition_spec D l Ω G H hGH
  let h₃ := stageTransition_spec D l Ω F H (hFG.trans hGH)
  let a := GeneralAlgebraicallyClosedCoefficients.scalarAssociator
    l EF EG EH i j m hm (Spec (.of D.k))
  have ha : HEq (S.assoc hFG hGH) a :=
    smallStageAssociator_heq D l Ω F G H hFG hGH
  have he₁ := smallStageComparison_heq D l hl Ω F G hFG
  have he₂ := smallStageComparison_heq D l hl Ω G H hGH
  have he₃ := smallStageComparison_heq D l hl Ω F H (hFG.trans hGH)
  have hn := rationalFibre_tower_transport D l hl EF EG i EH j m hm K
  refine towerHEqAll
    (C₀ := GeneralAlgebraicallyClosedCoefficients.Stage l Ω (Spec (.of D.k)) F)
    (C₁ := GeneralAlgebraicallyClosedCoefficients.Stage l Ω (Spec (.of D.k)) G)
    (C₂ := GeneralAlgebraicallyClosedCoefficients.Stage l Ω (Spec (.of D.k)) H)
    (c₀ := GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω (Spec (.of D.k)) F)
    (c₁ := GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω (Spec (.of D.k)) G)
    (c₂ := GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω (Spec (.of D.k)) H)
    (d₀ := nativeTargetCategory% (pointRationalFibre D l hl EF))
    (d₁ := nativeTargetCategory% (pointRationalFibre D l hl EG))
    (d₂ := nativeTargetCategory% (pointRationalFibre D l hl EH))
    (C₀' := nativeSourceType% (nativeTowerArg% 3 hn))
    (D₀' := nativeTargetType% (nativeTowerArg% 3 hn))
    (C₁' := nativeSourceType% (nativeTowerArg% 4 hn))
    (D₁' := nativeTargetType% (nativeTowerArg% 4 hn))
    (C₂' := nativeSourceType% (nativeTowerArg% 5 hn))
    (D₂' := nativeTargetType% (nativeTowerArg% 5 hn))
    (c₀' := nativeSourceCategory% (nativeTowerArg% 3 hn))
    (c₁' := nativeSourceCategory% (nativeTowerArg% 4 hn))
    (c₂' := nativeSourceCategory% (nativeTowerArg% 5 hn))
    (d₀' := nativeTargetCategory% (nativeTowerArg% 3 hn))
    (d₁' := nativeTargetCategory% (nativeTowerArg% 4 hn))
    (d₂' := nativeTargetCategory% (nativeTowerArg% 5 hn))
    rfl rfl rfl HEq.rfl HEq.rfl HEq.rfl
    rfl rfl rfl HEq.rfl HEq.rfl HEq.rfl
    (S.T hFG) (S.T hGH) (S.T (hFG.trans hGH))
    (nativeTowerArg% 0 hn) (nativeTowerArg% 1 hn) (nativeTowerArg% 2 hn)
    (pointRationalFibre D l hl EF) (pointRationalFibre D l hl EG)
    (pointRationalFibre D l hl EH)
    (nativeTowerArg% 3 hn) (nativeTowerArg% 4 hn) (nativeTowerArg% 5 hn)
    (DerivedCategory.pointFdScalarExtension i.toRingHom)
    (DerivedCategory.pointFdScalarExtension j.toRingHom)
    (DerivedCategory.pointFdScalarExtension m.toRingHom)
    (nativeTowerArg% 6 hn) (nativeTowerArg% 7 hn) (nativeTowerArg% 8 hn)
    (S.assoc hFG hGH) (nativeTowerArg% 9 hn)
    (smallStageComparison D l hl Ω F G hFG)
    (smallStageComparison D l hl Ω G H hGH)
    (smallStageComparison D l hl Ω F H (hFG.trans hGH))
    (nativeTowerArg% 10 hn) (nativeTowerArg% 11 hn) (nativeTowerArg% 12 hn)
    (pointFibreFdTensorTower i.toRingHom j.toRingHom ≪≫
      eqToIso (congrArg DerivedCategory.pointFdScalarExtension
        (congrArg AlgHom.toRingHom hm)))
    (nativeTowerArg% 13 hn)
    (heq_of_eq h₁) (heq_of_eq h₂) (heq_of_eq h₃)
    HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl ha he₁ he₂ he₃ K K HEq.rfl ?_
  exact hn

private theorem stageTensorSquare_eq
    (F G : AlgebraicallyClosedCoefficients.Index l Ω) (h : F ≤ G) :
    pointStageTensorSquare l Ω F G h =
      fdSquare
        (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω F G h).toRingHom
        (IntermediateField.inclusion h).toRingHom
        (Shrink.algEquiv ℚ_[l] F.val).toRingHom
        (Shrink.algEquiv ℚ_[l] G.val).toRingHom
        (pointStageCoefficientSquare l Ω F G h) := by rfl

-- The Shrink coefficient square has large dependent source and target categories.

private theorem stageTensorSquare_tower
    (F G H : AlgebraicallyClosedCoefficients.Index l Ω) (hFG : F ≤ G) (hGH : G ≤ H)
    (X : (DerivedCategory.pointFiniteDimensional
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)).FullSubcategory) :
    (DerivedCategory.pointFdScalarExtension (Shrink.algEquiv ℚ_[l] H.val).toRingHom).map
      ((pointFibreFdTensorTower
          (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω F G hFG).toRingHom
          (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω G H hGH).toRingHom ≪≫
        eqToIso (congrArg DerivedCategory.pointFdScalarExtension
          (congrArg AlgHom.toRingHom
            ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2
              F G H hFG hGH)))).hom.app X) ≫
      (pointStageTensorSquare l Ω F H (hFG.trans hGH)).hom.app X =
    (pointStageTensorSquare l Ω G H hGH).hom.app
        ((DerivedCategory.pointFdScalarExtension
          (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω F G hFG).toRingHom).obj X) ≫
      (DerivedCategory.pointFdScalarExtension (IntermediateField.inclusion hGH).toRingHom).map
        ((pointStageTensorSquare l Ω F G hFG).hom.app X) ≫
      (actualFdTower l Ω F G H hFG hGH).hom.app
          ((DerivedCategory.pointFdScalarExtension
            (Shrink.algEquiv ℚ_[l] F.val).toRingHom).obj X) := by
  rw [stageTensorSquare_eq, stageTensorSquare_eq, stageTensorSquare_eq]
  unfold actualFdTower
  exact fdSquare_tower_transport_left
      (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω F G hFG).toRingHom
      (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω G H hGH).toRingHom
      (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω F H
        (hFG.trans hGH)).toRingHom
      (IntermediateField.inclusion hFG).toRingHom
      (IntermediateField.inclusion hGH).toRingHom
      (IntermediateField.inclusion (hFG.trans hGH)).toRingHom
      (Shrink.algEquiv ℚ_[l] F.val).toRingHom
      (Shrink.algEquiv ℚ_[l] G.val).toRingHom
      (Shrink.algEquiv ℚ_[l] H.val).toRingHom
      (congrArg AlgHom.toRingHom
        ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2 F G H hFG hGH))
      (by rfl)
      (pointStageCoefficientSquare l Ω F G hFG)
      (pointStageCoefficientSquare l Ω G H hGH)
      (pointStageCoefficientSquare l Ω F H (hFG.trans hGH)) X

private theorem stageFibre_eq
    (F : AlgebraicallyClosedCoefficients.Index l Ω) :
    pointStageFibre D l hl Ω F =
      pointRationalFibre D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) ⋙
        DerivedCategory.pointFdScalarExtension (Shrink.algEquiv ℚ_[l] F.val).toRingHom := by rfl

private theorem stageComparison_eq
    (F G : AlgebraicallyClosedCoefficients.Index l Ω) (h : F ≤ G) :
    pointStageFibreScalarIso D l hl Ω F G h =
      liftedComparison
        (GeneralAlgebraicallyClosedCoefficients.stageTransition l Ω (Spec (.of D.k)) F G h)
        (pointRationalFibre D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F))
        (pointRationalFibre D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω G))
        (DerivedCategory.pointFdScalarExtension
          (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω F G h).toRingHom)
        (DerivedCategory.pointFdScalarExtension (Shrink.algEquiv ℚ_[l] F.val).toRingHom)
        (DerivedCategory.pointFdScalarExtension (Shrink.algEquiv ℚ_[l] G.val).toRingHom)
        (DerivedCategory.pointFdScalarExtension (IntermediateField.inclusion h).toRingHom)
        (smallStageComparison D l hl Ω F G h) (pointStageTensorSquare l Ω F G h) := by
  unfold pointStageFibreScalarIso liftedComparison smallStageComparison
  rfl

private theorem fdStageComp_hom
    {E F : AlgebraicallyClosedCoefficients.Index l Ω} (h : E ≤ F)
    (X : (DerivedCategory.pointFiniteDimensional E.val).FullSubcategory) :
    ((DerivedCategory.pointFdQbarStageComp l Ω h).hom.app X).hom =
      (DerivedCategory.fieldScalarTower (IntermediateField.inclusion h).toRingHom
        F.val.subtype).hom.app X.obj := by
  have he := ((fullyFaithfulInducedFunctor (DerivedCategory.pointFdQbarObject l Ω)).whiskeringRight
    ((DerivedCategory.pointFiniteDimensional E.val).FullSubcategory)).map_preimage
      (X := DerivedCategory.pointFdScalarExtension (IntermediateField.inclusion h).toRingHom ⋙
        DerivedCategory.pointFdQbarStage l Ω F)
      (Y := DerivedCategory.pointFdQbarStage l Ω E)
      (Functor.isoWhiskerLeft (DerivedCategory.pointFiniteDimensional E.val).ι
        (DerivedCategory.fieldScalarTower (IntermediateField.inclusion h).toRingHom
          F.val.subtype)).hom
  simpa only [DerivedCategory.pointFdQbarStageComp, inducedFunctor,
    Functor.FullyFaithful.preimageIso,
    Functor.whiskeringRight_obj_map, Functor.whiskeringRight_obj_obj,
    Functor.comp_obj, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    ObjectProperty.ι_map, ObjectProperty.ι_obj] using
    congrArg (fun t ↦ t.app X) he

private theorem fdStage_map
    (E : AlgebraicallyClosedCoefficients.Index l Ω)
    {X Y : (DerivedCategory.pointFiniteDimensional E.val).FullSubcategory} (f : X ⟶ Y) :
    ((DerivedCategory.pointFdQbarStage l Ω E).map f).hom =
      (DerivedCategory.fieldDerivedScalarExtension E.val.subtype).map f.hom := rfl

private theorem fdStage_obj
    (E : AlgebraicallyClosedCoefficients.Index l Ω)
    (X : (DerivedCategory.pointFiniteDimensional E.val).FullSubcategory) :
    DerivedCategory.pointFdQbarObject l Ω ((DerivedCategory.pointFdQbarStage l Ω E).obj X) =
      (DerivedCategory.fieldDerivedScalarExtension E.val.subtype).obj X.obj := rfl

private theorem fdStage_tower
    (F G H : AlgebraicallyClosedCoefficients.Index l Ω) (hFG : F ≤ G) (hGH : G ≤ H)
    (X : (DerivedCategory.pointFiniteDimensional F.val).FullSubcategory) :
    (DerivedCategory.pointFdQbarStage l Ω H).map
        ((actualFdTower l Ω F G H hFG hGH).hom.app X) ≫
        (DerivedCategory.pointFdQbarStageComp l Ω (hFG.trans hGH)).hom.app X =
      (DerivedCategory.pointFdQbarStageComp l Ω hGH).hom.app
          ((DerivedCategory.pointFdScalarExtension
            (IntermediateField.inclusion hFG).toRingHom).obj X) ≫
        (DerivedCategory.pointFdQbarStageComp l Ω hFG).hom.app X := by
  rw [actualFdTower_eq]
  apply InducedCategory.hom_ext
  simp only [InducedCategory.comp_hom, fdStage_map, fdStageComp_hom,
    fdTower_hom, fdScalar_obj, Functor.comp_obj, fdStage_obj]
  have ht := congrArg (fun e ↦ e.hom.app X.obj)
    (DerivedCategory.fieldScalarTower_assoc (IntermediateField.inclusion hFG).toRingHom
      (IntermediateField.inclusion hGH).toRingHom H.val.subtype)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp,
    Functor.comp_obj] at ht
  exact ht

-- Keep the coefficient expressions explicit: local type aliases cause expensive kernel
-- conversions between the component tower equations and their composite.

private theorem stageFibre_tower
    (F G H : AlgebraicallyClosedCoefficients.Index l Ω) (hFG : F ≤ G) (hGH : G ≤ H)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω (Spec (.of D.k)) F) :
    (pointStageFibre D l hl Ω H).map
      (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (Spec (.of D.k))).assoc
        hFG hGH).hom.app K) ≫
      (pointStageFibreScalarIso D l hl Ω F H (hFG.trans hGH)).hom.app K =
    (pointStageFibreScalarIso D l hl Ω G H hGH).hom.app
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (Spec (.of D.k))).T hFG).obj K) ≫
      (DerivedCategory.pointFdScalarExtension (IntermediateField.inclusion hGH).toRingHom).map
        ((pointStageFibreScalarIso D l hl Ω F G hFG).hom.app K) ≫
      (actualFdTower l Ω F G H hFG hGH).hom.app
          ((pointStageFibre D l hl Ω F).obj K) := by
  exact liftedTower
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (Spec (.of D.k))).T hFG)
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (Spec (.of D.k))).T hGH)
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω
      (Spec (.of D.k))).T (hFG.trans hGH))
    (pointRationalFibre D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F))
    (pointRationalFibre D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω G))
    (pointRationalFibre D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω H))
    (DerivedCategory.pointFdScalarExtension
      (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω F G hFG).toRingHom)
    (DerivedCategory.pointFdScalarExtension
      (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω G H hGH).toRingHom)
    (DerivedCategory.pointFdScalarExtension
      (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω F H (hFG.trans hGH)).toRingHom)
    (DerivedCategory.pointFdScalarExtension (Shrink.algEquiv ℚ_[l] F.val).toRingHom)
    (DerivedCategory.pointFdScalarExtension (Shrink.algEquiv ℚ_[l] G.val).toRingHom)
    (DerivedCategory.pointFdScalarExtension (Shrink.algEquiv ℚ_[l] H.val).toRingHom)
    (DerivedCategory.pointFdScalarExtension (IntermediateField.inclusion hFG).toRingHom)
    (DerivedCategory.pointFdScalarExtension (IntermediateField.inclusion hGH).toRingHom)
    (DerivedCategory.pointFdScalarExtension
      (IntermediateField.inclusion (hFG.trans hGH)).toRingHom)
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (Spec (.of D.k))).assoc hFG hGH)
    (pointFibreFdTensorTower
      (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω F G hFG).toRingHom
      (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω G H hGH).toRingHom ≪≫
      eqToIso (congrArg DerivedCategory.pointFdScalarExtension
        (congrArg AlgHom.toRingHom
          ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2 F G H hFG hGH))))
    (actualFdTower l Ω F G H hFG hGH)
    (smallStageComparison D l hl Ω F G hFG) (smallStageComparison D l hl Ω G H hGH)
    (smallStageComparison D l hl Ω F H (hFG.trans hGH))
    (pointStageTensorSquare l Ω F G hFG) (pointStageTensorSquare l Ω G H hGH)
    (pointStageTensorSquare l Ω F H (hFG.trans hGH))
    (pointStageFibre D l hl Ω F) (pointStageFibre D l hl Ω G) (pointStageFibre D l hl Ω H)
    (stageFibre_eq D l hl Ω F) (stageFibre_eq D l hl Ω G) (stageFibre_eq D l hl Ω H)
    (pointStageFibreScalarIso D l hl Ω F G hFG)
    (pointStageFibreScalarIso D l hl Ω G H hGH)
    (pointStageFibreScalarIso D l hl Ω F H (hFG.trans hGH))
    (heq_of_eq (stageComparison_eq D l hl Ω F G hFG))
    (heq_of_eq (stageComparison_eq D l hl Ω G H hGH))
    (heq_of_eq (stageComparison_eq D l hl Ω F H (hFG.trans hGH))) K
    (smallStage_tower D l hl Ω F G H hFG hGH K)
    (stageTensorSquare_tower l Ω F G H hFG hGH _)

-- Kernel checking the composite tower reduces the concrete common-stage category instances.

private theorem totalComparison_tower
    (F G H : AlgebraicallyClosedCoefficients.Index l Ω) (hFG : F ≤ G) (hGH : G ≤ H)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω (Spec (.of D.k)) F) :
    (pointStageFibre D l hl Ω H ⋙ DerivedCategory.pointFdQbarStage l Ω H).map
      (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (Spec (.of D.k))).assoc
        hFG hGH).hom.app K) ≫
      (finishedComparison
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω
          (Spec (.of D.k))).T (hFG.trans hGH))
        (pointStageFibre D l hl Ω F) (pointStageFibre D l hl Ω H)
        (DerivedCategory.pointFdScalarExtension
          (IntermediateField.inclusion (hFG.trans hGH)).toRingHom)
        (DerivedCategory.pointFdQbarStage l Ω F) (DerivedCategory.pointFdQbarStage l Ω H)
        (pointStageFibreScalarIso D l hl Ω F H (hFG.trans hGH))
        (DerivedCategory.pointFdQbarStageComp l Ω (hFG.trans hGH))).hom.app K =
    (finishedComparison
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (Spec (.of D.k))).T hGH)
        (pointStageFibre D l hl Ω G) (pointStageFibre D l hl Ω H)
        (DerivedCategory.pointFdScalarExtension (IntermediateField.inclusion hGH).toRingHom)
        (DerivedCategory.pointFdQbarStage l Ω G) (DerivedCategory.pointFdQbarStage l Ω H)
        (pointStageFibreScalarIso D l hl Ω G H hGH)
        (DerivedCategory.pointFdQbarStageComp l Ω hGH)).hom.app
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω
          (Spec (.of D.k))).T hFG).obj K) ≫
      (finishedComparison
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (Spec (.of D.k))).T hFG)
        (pointStageFibre D l hl Ω F) (pointStageFibre D l hl Ω G)
        (DerivedCategory.pointFdScalarExtension (IntermediateField.inclusion hFG).toRingHom)
        (DerivedCategory.pointFdQbarStage l Ω F) (DerivedCategory.pointFdQbarStage l Ω G)
        (pointStageFibreScalarIso D l hl Ω F G hFG)
        (DerivedCategory.pointFdQbarStageComp l Ω hFG)).hom.app K := by
  exact finishedTower
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (Spec (.of D.k))).T hFG)
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (Spec (.of D.k))).T hGH)
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω
      (Spec (.of D.k))).T (hFG.trans hGH))
    (pointStageFibre D l hl Ω F) (pointStageFibre D l hl Ω G) (pointStageFibre D l hl Ω H)
    (DerivedCategory.pointFdScalarExtension (IntermediateField.inclusion hFG).toRingHom)
    (DerivedCategory.pointFdScalarExtension (IntermediateField.inclusion hGH).toRingHom)
    (DerivedCategory.pointFdScalarExtension
      (IntermediateField.inclusion (hFG.trans hGH)).toRingHom)
    (DerivedCategory.pointFdQbarStage l Ω F) (DerivedCategory.pointFdQbarStage l Ω G)
    (DerivedCategory.pointFdQbarStage l Ω H)
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (Spec (.of D.k))).assoc hFG hGH)
    (actualFdTower l Ω F G H hFG hGH)
    (pointStageFibreScalarIso D l hl Ω F G hFG)
    (pointStageFibreScalarIso D l hl Ω G H hGH)
    (pointStageFibreScalarIso D l hl Ω F H (hFG.trans hGH))
    (DerivedCategory.pointFdQbarStageComp l Ω hFG)
    (DerivedCategory.pointFdQbarStageComp l Ω hGH)
    (DerivedCategory.pointFdQbarStageComp l Ω (hFG.trans hGH)) K
    (stageFibre_tower D l hl Ω F G H hFG hGH K)
    (fdStage_tower l Ω F G H hFG hGH ((pointStageFibre D l hl Ω F).obj K))


-- The final specialization checks the concrete source and target stage functor instances.

/-- Enlarging a common coefficient field leaves the displayed point-fibre arrow unchanged.
Source: sections-scalar-extension tower compatibility and common-stage transport,
expanded in the proof of the finite-coefficient point construction, clause 4.
(blueprint: lem-weil-point-fibre-representative-transport).

Proof: write alpha for the source stage associator, phi for pointStageFibreScalarIso,
and tau for the target tensor tower. The normalization of phi by the rational sections
comparison, its tower equation, the pure-tensor normalization of the carrier-lift
comparison, and the Shrink coefficient square give the tower equation for phi.
Apply it to the two endpoints of f. Substitute source transport
alpha_source inverse, T(f), alpha_target into the displayed representative. Naturality
of phi for the last extension moves T(f) across phi. Cancel the adjacent inverse phi
factors at both endpoints. The remaining tau factors cancel against the tower equation
for pointFdQbarStageComp, which is the fieldScalarTower associativity equation.
The resulting arrow is exactly the original representative. This works for reflexive
extensions and zero objects as well: all comparisons remain isomorphisms and the same
cancellation applies; no faithfulness of a scalar transition is used. -/
theorem pointQbarFibreRepresentative_transport
    (A B : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (G H : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ G) (hB : B.stage ≤ G)
    (h : G ≤ H) (f : A.toStage hA ⟶ B.toStage hB) :
    pointQbarFibreRepresentative D l hl Ω A B H (hA.trans h) (hB.trans h)
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (Spec (.of D.k))).tr h f) =
      pointQbarFibreRepresentative D l hl Ω A B G hA hB f := by
  exact finishedRepresentative_transport
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (Spec (.of D.k)))
    (fun F ↦ pointStageFibre D l hl Ω F)
    (fun F ↦ DerivedCategory.pointFdQbarStage l Ω F)
    (fun h ↦ DerivedCategory.pointFdScalarExtension (IntermediateField.inclusion h).toRingHom)
    (fun h ↦ pointStageFibreScalarIso D l hl Ω _ _ h)
    (fun h ↦ DerivedCategory.pointFdQbarStageComp l Ω h)
    (fun h k K ↦ totalComparison_tower D l hl Ω _ _ _ h k K)
    A.obj B.obj hA hB h f

end WeilConjectures
