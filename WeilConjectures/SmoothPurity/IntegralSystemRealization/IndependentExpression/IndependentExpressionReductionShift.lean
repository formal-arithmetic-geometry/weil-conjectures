/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralSystemRealization.IndependentExpression.IndependentExpressionShiftNaturality
import Mathlib.CategoryTheory.Comma.Arrow

/-! # Pointwise reduction and independent expression shifts

Source: blueprint purity transport, Step 2
(blueprint: lem-pur-independent-expression-reduction-shift).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization

attribute [local irreducible] Expression.SlotContext.shift IndependentExpression.shift

open Classical in
/-- Pointwise functors commute with shifting a single family coordinate.
Source: blueprint Step 2
(blueprint: lem-pur-independent-expression-reduction-shift). -/
def pointwiseInputShiftIso {I : Type u} {C D : I → Type v}
    [∀ i, Category.{w} (C i)] [∀ i, Category.{w} (D i)]
    [∀ i, HasShift (C i) ℤ] [∀ i, HasShift (D i) ℤ]
    (R : ∀ i, C i ⥤ D i) (a : ∀ i, (R i).CommShift ℤ) (i : I) (r : ℤ) :
    inputShift C i r ⋙ Functor.pi R ≅ Functor.pi R ⋙ inputShift D i r := by
  let χ (j : I) : inputShift C i r ⋙ Functor.pi R ⋙ Pi.eval D j ≅
      Functor.pi R ⋙ inputShift D i r ⋙ Pi.eval D j := by
    by_cases h : i = j
    · subst j
      change (Pi.eval C i ⋙
          (if i = i then shiftFunctor (C i) r else 𝟭 (C i))) ⋙ R i ≅
        Pi.eval C i ⋙ R i ⋙ (if i = i then shiftFunctor (D i) r else 𝟭 (D i))
      rw [if_pos rfl, if_pos rfl]
      exact Functor.isoWhiskerLeft (Pi.eval C i)
        (Functor.commShiftIso (R i) (self := a i) r)
    · change (Pi.eval C j ⋙
          (if i = j then shiftFunctor (C j) r else 𝟭 (C j))) ⋙ R j ≅
        Pi.eval C j ⋙ R j ⋙ (if i = j then shiftFunctor (D j) r else 𝟭 (D j))
      rw [if_neg h, if_neg h]
      exact Iso.refl _
  exact NatIso.ofComponents (fun K ↦ Pi.isoMk (fun j ↦ (χ j).app K))
    (by intro K N f; funext j; exact (χ j).hom.naturality f)

open Classical in
/-- Evaluation through a context commutes with pointwise replacement.
Source: blueprint Step 2
(blueprint: lem-pur-independent-expression-reduction-shift). -/
theorem IndependentExpression.pointwiseContext_evaluate
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    {C : I → Type v} [∀ i, Category.{w} (C i)]
    {D : Scheme.{u} → Type v} [∀ W, Category.{w} (D W)]
    (R : ∀ i, C i ⥤ D (X i).left) (d : Interpretation D) {W : Over B}
    (e : IndependentExpression B I X W) (K : ∀ i, C i) (i : I) (P : C i) :
    (e.variableContext d ((Functor.pi R).obj K) i).evaluate.obj ((R i).obj P) =
      (e.val.evaluate d).obj ((Functor.pi R).obj (Function.update K i P)) := by
  rw [(e.variableContext_evaluate d ((Functor.pi R).obj K) i ((R i).obj P)).1]
  apply congrArg (e.val.evaluate d).obj
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simp [Function.update_of_ne h]

open Classical in
private theorem context_has_label {B : Scheme.{u}} {I : Type u}
    {X : I → Over B} {C : Scheme.{u} → Type v} [∀ W, Category.{w} (C W)]
    (d : Interpretation C) (K : ∀ i, C (X i).left) (i : I)
    {W : Over B} (e : Expression B I X W) :
    (e.variableContext d K i).isSome ↔ ∃ j, e.occurrenceLabel j = i := by
  classical
  induction e with
  | var j =>
    by_cases h : i = j
    · subst j
      constructor
      · intro _; exact ⟨PUnit.unit, rfl⟩
      · intro _; simp [Expression.variableContext]
    · simp [Expression.variableContext, Expression.occurrenceLabel, h, Ne.symm h]
  | pull f e ih =>
    change (Option.map _ (e.variableContext d K i)).isSome ↔
      ∃ j : e.Occurrences, e.occurrenceLabel j = i
    rw [Option.isSome_map]
    exact ih
  | push f hp e ih =>
    change (Option.map _ (e.variableContext d K i)).isSome ↔
      ∃ j : e.Occurrences, e.occurrenceLabel j = i
    rw [Option.isSome_map]
    exact ih
  | shriek j hj hq e ih =>
    change (Option.map _ (e.variableContext d K i)).isSome ↔
      ∃ j : e.Occurrences, e.occurrenceLabel j = i
    rw [Option.isSome_map]
    exact ih
  | compactSupport f c e ih =>
    change (Option.map _ (e.variableContext d K i)).isSome ↔
      ∃ j : e.Occurrences, e.occurrenceLabel j = i
    rw [Option.isSome_map]
    exact ih
  | tensor e t ih jt =>
    cases he : e.variableContext d K i with
    | none =>
      have ha : ¬ ∃ j, e.occurrenceLabel j = i := by
        intro hex
        have bad := ih.mpr hex
        simp [he] at bad
      simp only [Expression.variableContext, he]
      rw [Option.isSome_map]
      constructor
      · intro ht
        obtain ⟨j, hj⟩ := jt.mp ht
        exact ⟨Sum.inr j, hj⟩
      · rintro ⟨j, hj⟩
        cases j with
        | inl j => exact (ha ⟨j, hj⟩).elim
        | inr j => exact jt.mpr ⟨j, hj⟩
    | some c =>
      have hex := ih.mp (by simp [he])
      constructor
      · intro _
        obtain ⟨j, hj⟩ := hex
        exact ⟨Sum.inl j, hj⟩
      · intro _
        simp [Expression.variableContext, he]


private def pairArrow {A : Type v} {B : Type v}
    [Category.{w} A] [Category.{w} B] (f : Arrow A) (g : Arrow B) : Arrow (A × B) :=
  Arrow.mk (CategoryTheory.Prod.mkHom f.hom g.hom)

private theorem evaluate_map_fixed {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    {D : Scheme.{u} → Type v} [∀ W, Category.{w} (D W)] (d : Interpretation D)
    (K M N : ∀ i, D (X i).left) (f : M ⟶ N) {W : Over B}
    (e : Expression B I X W)
    (h : ∀ j, Arrow.mk (f (e.occurrenceLabel j)) =
      Arrow.mk (𝟙 (K (e.occurrenceLabel j)))) :
    Arrow.mk ((e.evaluate d).map f) = Arrow.mk (𝟙 ((e.evaluate d).obj K)) := by
  induction e with
  | var j => exact h PUnit.unit
  | pull g e ih =>
    simpa [Expression.evaluate] using congrArg (d.pull g.left).mapArrow.obj (ih h)
  | push g hp e ih =>
    simpa [Expression.evaluate] using congrArg (d.push g.left).mapArrow.obj (ih h)
  | shriek j hj hq e ih =>
    let := hj
    simpa [Expression.evaluate] using congrArg (d.shriek j.left).mapArrow.obj (ih h)
  | compactSupport g c e ih =>
    simpa [Expression.evaluate] using congrArg (d.compactSupport g.left c).mapArrow.obj (ih h)
  | tensor e t ih jt =>
    have hp := congrArg₂ pairArrow (ih (fun j ↦ h (Sum.inl j)))
      (jt (fun j ↦ h (Sum.inr j)))
    simpa [pairArrow, Expression.evaluate] using congrArg (d.tensor _).mapArrow.obj hp

open Classical in
private theorem context_map_of_some {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    {D : Scheme.{u} → Type v} [∀ W, Category.{w} (D W)] (d : Interpretation D)
    (K M N : ∀ i, D (X i).left) (f : M ⟶ N) (i : I)
    {P Q : D (X i).left} (g : P ⟶ Q)
    (hs : Arrow.mk (f i) = Arrow.mk g)
    (ho : ∀ j, j ≠ i → Arrow.mk (f j) = Arrow.mk (𝟙 (K j)))
    {W : Over B} (e : Expression B I X W)
    (h : Function.Injective e.occurrenceLabel)
    (c : Expression.SlotContext d (X i) W) (hc : e.variableContext d K i = some c) :
    Arrow.mk ((e.evaluate d).map f) = Arrow.mk (c.evaluate.map g) := by
  induction e with
  | var j =>
    by_cases hij : i = j
    · subst j
      have hc' : c = .input := by simpa [Expression.variableContext] using hc.symm
      subst c
      exact hs
    · simp [Expression.variableContext, hij] at hc
  | pull k e ih =>
    obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.mp hc
    exact congrArg (d.pull k.left).mapArrow.obj (ih h c' hc')
  | push k hp e ih =>
    obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.mp hc
    exact congrArg (d.push k.left).mapArrow.obj (ih h c' hc')
  | shriek j hj hq e ih =>
    obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.mp hc
    let := hj
    exact congrArg (d.shriek j.left).mapArrow.obj (ih h c' hc')
  | compactSupport k a e ih =>
    obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.mp hc
    exact congrArg (d.compactSupport k.left a).mapArrow.obj (ih h c' hc')
  | tensor e t ih jt =>
    have hl : Function.Injective e.occurrenceLabel :=
      fun a b hab ↦ Sum.inl.inj (h (a₁ := Sum.inl a) (a₂ := Sum.inl b) hab)
    have hr : Function.Injective t.occurrenceLabel :=
      fun a b hab ↦ Sum.inr.inj (h (a₁ := Sum.inr a) (a₂ := Sum.inr b) hab)
    cases he : e.variableContext d K i with
    | some c' =>
      obtain ⟨j, hj⟩ := (context_has_label d K i e).mp (by simp [he])
      have ha : ∀ k, t.occurrenceLabel k ≠ i := by
        intro k hk
        have bad := h (a₁ := Sum.inl j) (a₂ := Sum.inr k) (hj.trans hk.symm)
        cases bad
      simp only [Expression.variableContext, he, Option.some.injEq] at hc
      subst c
      have hp := congrArg₂ pairArrow (ih hl c' he)
        (evaluate_map_fixed d K M N f t (fun k ↦ ho _ (ha k)))
      simpa [pairArrow, Expression.evaluate, Expression.SlotContext.evaluate] using
        congrArg (d.tensor _).mapArrow.obj hp
    | none =>
      have ha : ∀ k, e.occurrenceLabel k ≠ i := by
        intro k hk
        have bad := (context_has_label d K i e).mpr ⟨k, hk⟩
        simp [he] at bad
      simp only [Expression.variableContext, he] at hc
      obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.mp hc
      have hp := congrArg₂ pairArrow
        (evaluate_map_fixed d K M N f e (fun k ↦ ho _ (ha k))) (jt hr c' hc')
      simpa [pairArrow, Expression.evaluate, Expression.SlotContext.evaluate] using
        congrArg (d.tensor _).mapArrow.obj hp

private theorem iso_app_cast_arrow {A B : Type*} [Category* A] [Category* B]
    {F G F' G' : A ⥤ B} (hF : F = F') (hG : G = G') (t : F ≅ G)
    (h : (F ≅ G) = (F' ≅ G')) (K : A) :
    Arrow.mk ((cast h t).hom.app K) = Arrow.mk (t.hom.app K) := by
  subst F'
  subst G'
  rfl

open Classical in
/-- Moving the selected reduction shift through evaluation agrees with applying
pointwise reduction's shift isomorphism to the entire expression.
Source: blueprint purity transport, Step 2
(blueprint: lem-pur-independent-expression-reduction-shift).

Proof: regard the selected context as a functor out of its input coordinate.
It equals evaluation after the functor inserting that coordinate and holding the
others fixed: induct on the expression, using occurrence-label injectivity at a
tensor to show that its other subtree ignores the selected coordinate. The map
of the pointwise shift isomorphism has the reduction shift at the selected index
and identities at all other indices. Apply the functor equality to that map.
The object equalities in the displayed equation are precisely the insertion and
replacement equalities; functoriality of equality transport gives both endpoints.
This proves the component equation before either context shift or total limit. -/
theorem IndependentExpression.pointwiseShift_component
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    {C : I → Type v} [∀ i, Category.{w} (C i)] [∀ i, HasShift (C i) ℤ]
    {D : Scheme.{u} → Type v} [∀ W, Category.{w} (D W)] [∀ W, HasShift (D W) ℤ]
    (R : ∀ i, C i ⥤ D (X i).left) (a : ∀ i, (R i).CommShift ℤ)
    (d : Interpretation D) {W : Over B} (e : IndependentExpression B I X W)
    (K : ∀ i, C i) (i : I) (r : ℤ) :
    (e.val.evaluate d).map ((pointwiseInputShiftIso R a i r).hom.app K) ≫
        (e.val.evaluate d).map (eqToHom (inputShift_obj _ ((Functor.pi R).obj K) i r)) ≫
        eqToHom (e.variableContext_evaluate d ((Functor.pi R).obj K) i
          (((Functor.pi R).obj K i)⟦r⟧)).1.symm =
      (e.val.evaluate d).map ((Functor.pi R).map (eqToHom (inputShift_obj _ K i r))) ≫
        eqToHom (e.pointwiseContext_evaluate R d K i ((K i)⟦r⟧)).symm ≫
        (e.variableContext d ((Functor.pi R).obj K) i).evaluate.map
          ((Functor.commShiftIso (R i) (self := a i) r).hom.app (K i)) := by
  let f := (pointwiseInputShiftIso R a i r).hom.app K
  let g := (Functor.commShiftIso (R i) (self := a i) r).hom.app (K i)
  have hs : Arrow.mk (f i) = Arrow.mk g := by
    simp? [f, g, pointwiseInputShiftIso]
    apply iso_app_cast_arrow
    · change (Pi.eval C i ⋙ shiftFunctor (C i) r) ⋙ R i =
        (Pi.eval C i ⋙ (if i = i then shiftFunctor (C i) r else 𝟭 (C i))) ⋙ R i
      rw [if_pos rfl]
    · change Pi.eval C i ⋙ R i ⋙ shiftFunctor (D (X i).left) r =
        Pi.eval C i ⋙ R i ⋙
          (if i = i then shiftFunctor (D (X i).left) r else 𝟭 (D (X i).left))
      rw [if_pos rfl]
  have ho : ∀ j, j ≠ i → Arrow.mk (f j) =
      Arrow.mk (𝟙 (((Functor.pi R).obj K) j)) := by
    intro j hj
    simp? [f, pointwiseInputShiftIso, Ne.symm hj]
    apply iso_app_cast_arrow
    · change (Pi.eval C j ⋙ 𝟭 (C j)) ⋙ R j =
        (Pi.eval C j ⋙ (if i = j then shiftFunctor (C j) r else 𝟭 (C j))) ⋙ R j
      rw [if_neg (Ne.symm hj)]
    · change Pi.eval C j ⋙ R j ⋙ 𝟭 (D (X j).left) =
        Pi.eval C j ⋙ R j ⋙
          (if i = j then shiftFunctor (D (X j).left) r else 𝟭 (D (X j).left))
      rw [if_neg (Ne.symm hj)]
  have hm := context_map_of_some d ((Functor.pi R).obj K) _ _ f i g hs ho e.val
    e.property.injective (e.variableContext d ((Functor.pi R).obj K) i)
    (Option.some_get _).symm
  apply Arrow.mk_injective
  simpa only [eqToHom_map, eqToHom_trans, Arrow.arrow_mk_comp_eqToHom,
    Arrow.arrow_mk_eqToHom_comp] using hm

end WeilConjectures.IntegralSystemRealization
