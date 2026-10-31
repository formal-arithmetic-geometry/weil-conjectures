/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalScalarComparisonData

/-! # Horizontal pasting of scalar comparisons

Source: smooth purity transport, coefficient-pasting and coherence paragraphs
(blueprint: lem-pur-horizontal-scalar-pasting-calculus).
-/

@[expose] public section
set_option autoImplicit false
universe v w
open CategoryTheory CategoryTheory.Functor
namespace WeilConjectures.HorizontalScalarPasting
open RationalScalarComparisonIdentification

/-- The horizontal scalar comparison preserves the specified coefficient units.
Source: smooth purity transport, coefficient-pasting calculation
(blueprint: lem-pur-horizontal-scalar-pasting-calculus).
Proof: expand both horizontal components. Use functoriality and associativity,
substitute the two constituent equations, and apply naturality at the middle map.
For shifts insert the functor associators and use the whiskering and composition
instances of Mathlib; their identity components cancel. -/
theorem horizontal_unit
    {A B V : Type v} [Category.{w} A] [Category.{w} B] [Category.{w} V]
    (F : A ⥤ B) (G : B ⥤ V) (TA : A ⥤ A) (TB : B ⥤ B) (TV : V ⥤ V)
    (a : F ⋙ TB ≅ TA ⋙ F) (b : G ⋙ TV ≅ TB ⋙ G)
    (ua : TA ≅ 𝟭 A) (ub : TB ≅ 𝟭 B) (uv : TV ≅ 𝟭 V)
    (ha : UnitEquation a ub ua) (hb : UnitEquation b uv ub) :
    UnitEquation (H := F ⋙ G) (isoWhiskerLeft F b ≪≫ isoWhiskerRight a G) uv ua := by
  intro K
  change (b.hom.app (F.obj K) ≫ G.map (a.hom.app K)) ≫
    G.map (F.map (ua.hom.app K)) = uv.hom.app (G.obj (F.obj K))
  rw [Category.assoc]
  rw [← G.map_comp, ha K, hb (F.obj K)]

/-- Horizontal scalar comparison preserves the specified successive-extension equations.
Source: smooth purity transport, coefficient-pasting calculation
(blueprint: lem-pur-horizontal-scalar-pasting-calculus).
Proof: expand both horizontal components. Use functoriality and associativity,
substitute the two constituent equations, and apply naturality at the middle map.
For shifts insert the functor associators and use the whiskering and composition
instances of Mathlib; their identity components cancel. -/
theorem horizontal_composition
    {A₀ A₁ A₂ B₀ B₁ B₂ V₀ V₁ V₂ : Type v}
    [Category.{w} A₀] [Category.{w} A₁] [Category.{w} A₂]
    [Category.{w} B₀] [Category.{w} B₁] [Category.{w} B₂]
    [Category.{w} V₀] [Category.{w} V₁] [Category.{w} V₂]
    (F₀ : A₀ ⥤ B₀) (F₁ : A₁ ⥤ B₁) (F₂ : A₂ ⥤ B₂)
    (G₀ : B₀ ⥤ V₀) (G₁ : B₁ ⥤ V₁) (G₂ : B₂ ⥤ V₂)
    (TA : A₀ ⥤ A₁) (TB : B₀ ⥤ B₁) (TV : V₀ ⥤ V₁)
    (UA : A₁ ⥤ A₂) (UB : B₁ ⥤ B₂) (UV : V₁ ⥤ V₂)
    (VA : A₀ ⥤ A₂) (VB : B₀ ⥤ B₂) (VV : V₀ ⥤ V₂)
    (aF : F₀ ⋙ TB ≅ TA ⋙ F₁) (bF : F₁ ⋙ UB ≅ UA ⋙ F₂)
    (cF : F₀ ⋙ VB ≅ VA ⋙ F₂)
    (aG : G₀ ⋙ TV ≅ TB ⋙ G₁) (bG : G₁ ⋙ UV ≅ UB ⋙ G₂)
    (cG : G₀ ⋙ VV ≅ VB ⋙ G₂)
    (ea : TA ⋙ UA ≅ VA) (eb : TB ⋙ UB ≅ VB) (ev : TV ⋙ UV ≅ VV)
    (hF : CompositionEquation aF bF cF eb ea)
    (hG : CompositionEquation aG bG cG ev eb) :
    CompositionEquation (HE := F₀ ⋙ G₀) (HF := F₁ ⋙ G₁) (HL := F₂ ⋙ G₂)
      (isoWhiskerLeft F₀ aG ≪≫ isoWhiskerRight aF G₁)
      (isoWhiskerLeft F₁ bG ≪≫ isoWhiskerRight bF G₂)
      (isoWhiskerLeft F₀ cG ≪≫ isoWhiskerRight cF G₂) ev ea := by
  intro K
  change ev.hom.app (G₀.obj (F₀.obj K)) ≫
      (cG.hom.app (F₀.obj K) ≫ G₂.map (cF.hom.app K)) =
    UV.map (aG.hom.app (F₀.obj K) ≫ G₁.map (aF.hom.app K)) ≫
      (bG.hom.app (F₁.obj (TA.obj K)) ≫ G₂.map (bF.hom.app (TA.obj K))) ≫
      G₂.map (F₂.map (ea.hom.app K))
  have hn := bG.hom.naturality (aF.hom.app K)
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hG (F₀.obj K)]
  simp only [Functor.map_comp, Category.assoc]
  rw [← G₂.map_comp, hF K]
  simp only [Functor.map_comp]
  rw [reassoc_of% hn]

/-- Horizontal scalar comparison preserves the three specified shift structures.
Source: smooth purity transport, coefficient-pasting calculation
(blueprint: lem-pur-horizontal-scalar-pasting-calculus).
Proof: expand both horizontal components. Use functoriality and associativity,
substitute the two constituent equations, and apply naturality at the middle map.
For shifts insert the functor associators and use the whiskering and composition
instances of Mathlib; their identity components cancel. -/
theorem horizontal_shift
    {A B V A' B' V' : Type*}
    [Category* A] [Category* B] [Category* V]
    [Category* A'] [Category* B'] [Category* V']
    [HasShift A ℤ] [HasShift B ℤ] [HasShift V ℤ]
    [HasShift A' ℤ] [HasShift B' ℤ] [HasShift V' ℤ]
    (F : A ⥤ B) (G : B ⥤ V) (F' : A' ⥤ B') (G' : B' ⥤ V')
    (TA : A ⥤ A') (TB : B ⥤ B') (TV : V ⥤ V')
    [F.CommShift ℤ] [G.CommShift ℤ] [F'.CommShift ℤ] [G'.CommShift ℤ]
    [TA.CommShift ℤ] [TB.CommShift ℤ] [TV.CommShift ℤ]
    (a : F ⋙ TB ≅ TA ⋙ F') (b : G ⋙ TV ≅ TB ⋙ G')
    [NatTrans.CommShift a.hom ℤ] [NatTrans.CommShift b.hom ℤ] :
    @NatTrans.CommShift _ _ _ _ ((F ⋙ G) ⋙ TV) (TA ⋙ (F' ⋙ G'))
      (isoWhiskerLeft F b ≪≫ isoWhiskerRight a G').hom ℤ _ _ _
      (Functor.CommShift.comp (F ⋙ G) TV) (Functor.CommShift.comp TA (F' ⋙ G')) := by
  have hh : NatTrans.CommShift
      ((Functor.associator F G TV).hom ≫ Functor.whiskerLeft F b.hom ≫
        (Functor.associator F TB G').inv ≫ Functor.whiskerRight a.hom G' ≫
        (Functor.associator TA F' G').hom) ℤ := inferInstance
  have he : (Functor.associator F G TV).hom ≫ Functor.whiskerLeft F b.hom ≫
      (Functor.associator F TB G').inv ≫ Functor.whiskerRight a.hom G' ≫
        (Functor.associator TA F' G').hom =
      (isoWhiskerLeft F b ≪≫ isoWhiskerRight a G').hom := by
    ext K
    simp
  rw [he] at hh
  exact hh

/-- The horizontal composite of two purity squares is a purity square.
Source: smooth purity transport, coefficient-pasting calculation
(blueprint: lem-pur-horizontal-scalar-pasting-calculus).
Proof: expand both horizontal components. Use functoriality and associativity,
substitute the two constituent equations, and apply naturality at the middle map.
For shifts insert the functor associators and use the whiskering and composition
instances of Mathlib; their identity components cancel. -/
theorem horizontal_purity
    {A B V A' B' V' : Type v}
    [Category.{w} A] [Category.{w} B] [Category.{w} V]
    [Category.{w} A'] [Category.{w} B'] [Category.{w} V']
    (F J : A ⥤ B) (G K : B ⥤ V) (F' J' : A' ⥤ B') (G' K' : B' ⥤ V')
    (TA : A ⥤ A') (TB : B ⥤ B') (TV : V ⥤ V')
    (p : F ≅ J) (q : G ≅ K) (p' : F' ≅ J') (q' : G' ≅ K')
    (a : F ⋙ TB ≅ TA ⋙ F') (b : J ⋙ TB ≅ TA ⋙ J')
    (c : G ⋙ TV ≅ TB ⋙ G') (d : K ⋙ TV ≅ TB ⋙ K')
    (hF : PuritySquares p p' a b) (hG : PuritySquares q q' c d) (M : A) :
    TV.map ((isoWhiskerRight p G ≪≫ isoWhiskerLeft J q).hom.app M) ≫
        (isoWhiskerLeft J d ≪≫ isoWhiskerRight b K').hom.app M =
      (isoWhiskerLeft F c ≪≫ isoWhiskerRight a G').hom.app M ≫
        (isoWhiskerRight p' G' ≪≫ isoWhiskerLeft J' q').hom.app (TA.obj M) := by
  change TV.map (G.map (p.hom.app M) ≫ q.hom.app (J.obj M)) ≫
      (d.hom.app (J.obj M) ≫ K'.map (b.hom.app M)) =
    (c.hom.app (F.obj M) ≫ G'.map (a.hom.app M)) ≫
      (G'.map (p'.hom.app (TA.obj M)) ≫ q'.hom.app (J'.obj (TA.obj M)))
  rw [TV.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (TV.map (q.hom.app (J.obj M))), hG.1]
  simp only [Category.assoc]
  have hc := c.hom.naturality (p.hom.app M)
  dsimp only [Functor.comp_map] at hc
  rw [← Category.assoc (TV.map (G.map (p.hom.app M))), hc]
  simp only [Category.assoc]
  have hq := q'.hom.naturality (b.hom.app M)
  dsimp only [Functor.comp_obj] at hq
  rw [← hq]
  rw [← G'.map_comp_assoc, hF.1]
  simp only [G'.map_comp, Category.assoc]

/-- Horizontal composition of shift-compatible natural isomorphisms is shift compatible.
Source: smooth purity transport, final shift clause
(blueprint: lem-pur-horizontal-scalar-pasting-calculus).
Proof: insert the functor associator between the two whiskered transformations.
The whiskering, associator and composition shift instances apply, and the
associator has identity components. -/
theorem horizontal_iso_shift
    {A B V : Type*} [Category* A] [Category* B] [Category* V]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift V ℤ]
    (F J : A ⥤ B) (G K : B ⥤ V)
    [F.CommShift ℤ] [J.CommShift ℤ] [G.CommShift ℤ] [K.CommShift ℤ]
    (p : F ≅ J) (q : G ≅ K)
    [NatTrans.CommShift p.hom ℤ] [NatTrans.CommShift q.hom ℤ] :
    NatTrans.CommShift (isoWhiskerRight p G ≪≫ isoWhiskerLeft J q).hom ℤ := by
  have hh : NatTrans.CommShift
      (Functor.whiskerRight p.hom G ≫ Functor.whiskerLeft J q.hom) ℤ := inferInstance
  exact hh

end WeilConjectures.HorizontalScalarPasting
