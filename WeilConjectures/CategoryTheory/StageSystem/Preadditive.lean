/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import WeilConjectures.CategoryTheory.StageSystem.Functor

/-!
# The pair category of a stage system of preadditive categories

If the stages `C i` of a stage system `S` over a directed preorder are preadditive and the
transition functors are additive, the pair category `S.PairCategory` (the filtered `2`-colimit
of the stages) is preadditive: the morphisms `(i, x) ⟶ (j, y)` form the filtered colimit of the
abelian groups `Hom_{C n}(T x, T y)`, so that sums are computed at a common stage. If moreover
the stages have zero objects, so has the pair category, and the stage inclusions as well as the
functors induced by morphisms of stage systems of additive functors are additive.
-/

@[expose] public section

universe w v u v' u'

namespace CategoryTheory

open Category Limits ZeroObject

namespace StageSystem

variable {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
  [∀ i, Preadditive (C i)] {S : StageSystem C} [∀ {i j : I} (h : i ≤ j), (S.T h).Additive]

@[simp]
lemma tr_add {i j n p : I} {hi : i ≤ n} {hj : j ≤ n} (h : n ≤ p) {x : C i} {y : C j}
    (f g : (S.T hi).obj x ⟶ (S.T hj).obj y) : S.tr h (f + g) = S.tr h f + S.tr h g := by
  simp [tr]

@[simp]
lemma tr_neg {i j n p : I} {hi : i ≤ n} {hj : j ≤ n} (h : n ≤ p) {x : C i} {y : C j}
    (f : (S.T hi).obj x ⟶ (S.T hj).obj y) : S.tr h (-f) = -S.tr h f := by
  simp [tr]

@[simp]
lemma tr_zero {i j n p : I} {hi : i ≤ n} {hj : j ≤ n} (h : n ≤ p) {x : C i} {y : C j} :
    S.tr h (0 : (S.T hi).obj x ⟶ (S.T hj).obj y) = 0 := by
  simp [tr]

namespace PairCategory

variable [IsDirectedOrder I]

/-- The sum of two representatives, computed after transport to a common stage. -/
noncomputable def Rep.add {X Y : S.PairCategory} (r s : Rep X Y) : Rep X Y :=
  ⟨commonStage r.k s.k, r.hX.trans (le_commonStage_left _ _),
    r.hY.trans (le_commonStage_left _ _),
    S.tr (le_commonStage_left _ _) r.u + S.tr (le_commonStage_right _ _) s.u⟩

/-- The opposite of a representative. -/
def Rep.neg {X Y : S.PairCategory} (r : Rep X Y) : Rep X Y := ⟨r.k, r.hX, r.hY, -r.u⟩

lemma Rep.add_rel {X Y : S.PairCategory} {r r' s s' : Rep X Y}
    (hr : Rep.Rel r r') (hs : Rep.Rel s s') : Rep.Rel (r.add s) (r'.add s') := by
  obtain ⟨p, h₁, h₂, e⟩ := hr
  obtain ⟨q, h₃, h₄, e'⟩ := hs
  obtain ⟨a, ha₁, ha₂⟩ := exists_ge_ge p q
  obtain ⟨b, hb₁, hb₂⟩ := exists_ge_ge (commonStage r.k s.k) (commonStage r'.k s'.k)
  obtain ⟨m, hm₁, hm₂⟩ := exists_ge_ge a b
  refine ⟨m, hb₁.trans hm₂, hb₂.trans hm₂, ?_⟩
  change S.tr _ (S.tr _ r.u + S.tr _ s.u) = S.tr _ (S.tr _ r'.u + S.tr _ s'.u)
  rw [tr_add, tr_add, tr_tr, tr_tr, tr_tr, tr_tr]
  have E := Rep.rel_of_eq h₁ h₂ e (ha₁.trans hm₁)
  have E' := Rep.rel_of_eq h₃ h₄ e' (ha₂.trans hm₁)
  exact congr_arg₂ (· + ·) E E'

omit [IsDirectedOrder I] in
lemma Rep.neg_rel {X Y : S.PairCategory} {r r' : Rep X Y} (hr : Rep.Rel r r') :
    Rep.Rel r.neg r'.neg := by
  obtain ⟨p, h₁, h₂, e⟩ := hr
  exact ⟨p, h₁, h₂, by simp [Rep.neg, e]⟩

noncomputable instance (X Y : S.PairCategory) : Add (X ⟶ Y) :=
  ⟨Quotient.map₂ Rep.add (fun _ _ hr _ _ hs ↦ Rep.add_rel hr hs)⟩

noncomputable instance (X Y : S.PairCategory) : Neg (X ⟶ Y) :=
  ⟨Quotient.map Rep.neg (fun _ _ hr ↦ Rep.neg_rel hr)⟩

noncomputable instance (X Y : S.PairCategory) : Zero (X ⟶ Y) :=
  ⟨mkHom (commonStage X.stage Y.stage) (le_commonStage_left _ _) (le_commonStage_right _ _) 0⟩

lemma mkHom_add_mkHom {X Y : S.PairCategory} {n : I} {hX : X.stage ≤ n} {hY : Y.stage ≤ n}
    (u v : X.toStage hX ⟶ Y.toStage hY) :
    mkHom n hX hY u + mkHom n hX hY v = mkHom n hX hY (u + v) := by
  change mkHom _ _ _ _ = _
  rw [mkHom_eq_mkHom_iff']
  refine ⟨commonStage n n, le_rfl, le_commonStage_left _ _, ?_⟩
  simp only [tr_add, tr_tr]

lemma neg_mkHom {X Y : S.PairCategory} {n : I} {hX : X.stage ≤ n} {hY : Y.stage ≤ n}
    (u : X.toStage hX ⟶ Y.toStage hY) : -mkHom n hX hY u = mkHom n hX hY (-u) :=
  rfl

lemma zero_eq_mkHom {X Y : S.PairCategory} (n : I) (hX : X.stage ≤ n) (hY : Y.stage ≤ n) :
    (0 : X ⟶ Y) = mkHom n hX hY 0 := by
  change mkHom _ _ _ _ = _
  rw [mkHom_eq_mkHom_iff']
  obtain ⟨p, h, h'⟩ := exists_ge_ge (commonStage X.stage Y.stage) n
  exact ⟨p, h, h', by simp⟩

lemma mkHom_add_mkHom' {X Y : S.PairCategory} {n n' : I} {hX : X.stage ≤ n}
    {hY : Y.stage ≤ n} {hX' : X.stage ≤ n'} {hY' : Y.stage ≤ n'}
    (u : X.toStage hX ⟶ Y.toStage hY) (v : X.toStage hX' ⟶ Y.toStage hY')
    {p : I} (h : n ≤ p) (h' : n' ≤ p) :
    mkHom n hX hY u + mkHom n' hX' hY' v = mkHom p _ _ (S.tr h u + S.tr h' v) := by
  rw [← mkHom_tr h u, ← mkHom_tr h' v, mkHom_add_mkHom]

noncomputable instance (X Y : S.PairCategory) : AddCommGroup (X ⟶ Y) where
  add_assoc f g h := by
    induction f using hom_induction with
    | h n hX hY u =>
    induction g using hom_induction with
    | h n' hX' hY' v =>
    induction h using hom_induction with
    | h n'' hX'' hY'' w =>
      obtain ⟨a, ha, ha'⟩ := exists_ge_ge n n'
      obtain ⟨p, hp, hp'⟩ := exists_ge_ge a n''
      rw [← mkHom_tr (ha.trans hp) u, ← mkHom_tr (ha'.trans hp) v, ← mkHom_tr hp' w,
        mkHom_add_mkHom, mkHom_add_mkHom, mkHom_add_mkHom, mkHom_add_mkHom, add_assoc]
  zero_add f := by
    induction f using hom_induction with
    | h n hX hY u => rw [zero_eq_mkHom n hX hY, mkHom_add_mkHom, zero_add]
  add_zero f := by
    induction f using hom_induction with
    | h n hX hY u => rw [zero_eq_mkHom n hX hY, mkHom_add_mkHom, add_zero]
  add_comm f g := by
    induction f using hom_induction with
    | h n hX hY u =>
    induction g using hom_induction with
    | h n' hX' hY' v =>
      obtain ⟨p, hp, hp'⟩ := exists_ge_ge n n'
      rw [← mkHom_tr hp u, ← mkHom_tr hp' v, mkHom_add_mkHom, mkHom_add_mkHom, add_comm]
  neg_add_cancel f := by
    induction f using hom_induction with
    | h n hX hY u => rw [neg_mkHom, mkHom_add_mkHom, neg_add_cancel, ← zero_eq_mkHom]
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- The pair category of a stage system of preadditive categories along additive transition
functors is preadditive. -/
noncomputable instance : Preadditive S.PairCategory where
  add_comp X Y Z f f' g := by
    induction f using hom_induction with
    | h n hX hY u =>
    induction f' using hom_induction with
    | h n' hX' hY' u' =>
    induction g using hom_induction with
    | h n'' hY'' hZ w =>
      obtain ⟨a, ha, ha'⟩ := exists_ge_ge n n'
      obtain ⟨p, hp, hp'⟩ := exists_ge_ge a n''
      rw [← mkHom_tr (ha.trans hp) u, ← mkHom_tr (ha'.trans hp) u', ← mkHom_tr hp' w,
        mkHom_add_mkHom, mkHom_comp_mkHom, mkHom_comp_mkHom, mkHom_comp_mkHom,
        mkHom_add_mkHom, Preadditive.add_comp]
  comp_add X Y Z f g g' := by
    induction f using hom_induction with
    | h n hX hY u =>
    induction g using hom_induction with
    | h n' hY' hZ v =>
    induction g' using hom_induction with
    | h n'' hY'' hZ'' v' =>
      obtain ⟨a, ha, ha'⟩ := exists_ge_ge n n'
      obtain ⟨p, hp, hp'⟩ := exists_ge_ge a n''
      rw [← mkHom_tr (ha.trans hp) u, ← mkHom_tr (ha'.trans hp) v, ← mkHom_tr hp' v',
        mkHom_add_mkHom, mkHom_comp_mkHom, mkHom_comp_mkHom, mkHom_comp_mkHom,
        mkHom_add_mkHom, Preadditive.comp_add]

/-- An object of the pair category is zero as soon as it is zero at its stage. -/
lemma isZero_of_isZero {X : S.PairCategory} (hX : IsZero X.obj) : IsZero X := by
  rw [IsZero.iff_id_eq_zero, id_eq_mkHom X le_rfl, zero_eq_mkHom X.stage le_rfl le_rfl]
  exact congr_arg _ (IsZero.eq_of_src ((S.T le_rfl).map_isZero hX) _ _)

instance [Nonempty I] [∀ i, HasZeroObject (C i)] : HasZeroObject S.PairCategory :=
  ⟨⟨⟨Classical.arbitrary I, 0⟩, isZero_of_isZero (isZero_zero _)⟩⟩

end PairCategory

open PairCategory

variable [IsDirectedOrder I]

/-- The stage inclusions are additive. -/
instance (i : I) : (S.ι i).Additive where
  map_add {x y f g} := by
    rw [ι_map_eq le_rfl, ι_map_eq le_rfl, ι_map_eq le_rfl, Functor.map_add, mkHom_add_mkHom]

namespace Morphism

variable {D : I → Type u'} [∀ i, Category.{v'} (D i)] [∀ i, Preadditive (D i)]
  {S' : StageSystem D} [∀ {i j : I} (h : i ≤ j), (S'.T h).Additive] (F : Morphism S S')

/-- The functor induced by a morphism of stage systems of additive functors is additive. -/
instance [∀ i, (F.Φ i).Additive] : F.functor.Additive where
  map_add {X Y f g} := by
    induction f using hom_induction with
    | h n hX hY u =>
    induction g using hom_induction with
    | h n' hX' hY' v =>
      obtain ⟨p, hp, hp'⟩ := exists_ge_ge n n'
      rw [← mkHom_tr hp u, ← mkHom_tr hp' v, mkHom_add_mkHom, functor_map_mkHom,
        functor_map_mkHom, functor_map_mkHom, mkHom_add_mkHom]
      congr 1
      simp [mapAt]

end Morphism

end StageSystem

end CategoryTheory
