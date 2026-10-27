/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import Sheaf.CategoryTheory.PositiveFunctorRefinement

/-! # Independence of positive functor refinement evaluations

Source: main-20261015 blueprint, sec-trace-formula/sk-d-weil,
lem-trf-frobenius-operator-compact-description.proof.md, categorical expansion of the iterate
assertion (blueprint: lem-trf-positive-functor-refinement-independence).
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.PositiveFunctorRefinement

private theorem power_add_eq {C : Type u} [Category.{v} C] (T : C ⥤ C)
    (a b : ℕ) : NaturalTransport.power T b ⋙ NaturalTransport.power T a =
      NaturalTransport.power T (a + b) := by
  induction a with
  | zero => simpa only [NaturalTransport.power, Nat.zero_add] using
      Functor.comp_id (NaturalTransport.power T b)
  | succ a ih =>
    simpa only [NaturalTransport.power, Nat.succ_add, Functor.comp] using
      congrArg (· ⋙ T) ih

private theorem powerProduct_hom {C : Type u} [Category.{v} C] (T : C ⥤ C)
    (a b : ℕ) : (powerProductIso T a b).hom = eqToHom (power_add_eq T a b) := by
  induction a with
  | zero =>
    ext X
    simp [powerProductIso, NaturalTransport.power, eqToHom_app]
  | succ a ih =>
    ext X
    simp [powerProductIso, ih, eqToHom_app, eqToHom_map, eqToHom_trans,
      NaturalTransport.power]

-- Combine the outer and inner comparisons in functional order.
private def merge {C : Type u} [Category.{v} C] (T : C ⥤ C)
    {F G : C ⥤ C} {a b : ℕ}
    (α : F ⟶ NaturalTransport.power T a) (β : G ⟶ NaturalTransport.power T b) :
    G ⋙ F ⟶ NaturalTransport.power T (a + b) :=
  Functor.whiskerLeft G α ≫ Functor.whiskerRight β (NaturalTransport.power T a) ≫
    (powerProductIso T a b).hom

private theorem merge_outer {C : Type u} [Category.{v} C] (T : C ⥤ C)
    {F F' G : C ⥤ C} {a b : ℕ} (q : F ⟶ F')
    (α : F' ⟶ NaturalTransport.power T a) (β : G ⟶ NaturalTransport.power T b) :
    Functor.whiskerLeft G q ≫ merge T α β = merge T (q ≫ α) β := by
  ext X
  simp [merge, Category.assoc]

private theorem merge_inner {C : Type u} [Category.{v} C] (T : C ⥤ C)
    {F G G' : C ⥤ C} {a b : ℕ} (q : G ⟶ G')
    (α : F ⟶ NaturalTransport.power T a) (β : G' ⟶ NaturalTransport.power T b) :
    Functor.whiskerRight q F ≫ merge T α β = merge T α (q ≫ β) := by
  ext X
  simp only [merge, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  rw [← Category.assoc, α.naturality]
  simp only [Category.assoc]

private theorem merge_assoc {C : Type u} [Category.{v} C] (T : C ⥤ C)
    {F G H : C ⥤ C} {a b c : ℕ}
    (α : F ⟶ NaturalTransport.power T a) (β : G ⟶ NaturalTransport.power T b)
    (γ : H ⟶ NaturalTransport.power T c) :
    (Functor.associator H G F).inv ≫ merge T α (merge T β γ) ≫
        eqToHom (congrArg (NaturalTransport.power T) (Nat.add_assoc a b c).symm) =
      merge T (merge T α β) γ := by
  ext X
  simp only [merge, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Category.id_comp,
    Functor.map_comp, Category.assoc]
  rw [← (powerProductIso T a b).hom.naturality_assoc]
  simp [powerProduct_hom, eqToHom_app, eqToHom_map, eqToHom_trans]

-- The completion invariant is defined before choosing a refinement schedule.
private def completion {C : Type u} [Category.{v} C] (P : ℕ+ → C ⥤ C)
    (d : ∀ r : ℕ+, P r ≅ NaturalTransport.power (P 1) (r : ℕ)) :
    (E : Expression) → E.eval P ⟶ NaturalTransport.power (P 1) E.weight
  | .atom r => (d r).hom
  | .product A B => merge (P 1) (completion P d A) (completion P d B)

private theorem merge_outer_heq {C : Type u} [Category.{v} C] (T : C ⥤ C)
    {F F' G : C ⥤ C} {a a' b : ℕ} (w : a = a') (q : F ⟶ F')
    (α : F ⟶ NaturalTransport.power T a) (α' : F' ⟶ NaturalTransport.power T a')
    (β : G ⟶ NaturalTransport.power T b) (h : HEq (q ≫ α') α) :
    HEq (Functor.whiskerLeft G q ≫ merge T α' β) (merge T α β) := by
  subst a'
  rw [merge_outer, eq_of_heq h]

private theorem merge_inner_heq {C : Type u} [Category.{v} C] (T : C ⥤ C)
    {F G G' : C ⥤ C} {a b b' : ℕ} (w : b = b') (q : G ⟶ G')
    (α : F ⟶ NaturalTransport.power T a) (β : G ⟶ NaturalTransport.power T b)
    (β' : G' ⟶ NaturalTransport.power T b') (h : HEq (q ≫ β') β) :
    HEq (Functor.whiskerRight q F ≫ merge T α β') (merge T α β) := by
  subst b'
  rw [merge_inner, eq_of_heq h]

private theorem inverse_heq {C : Type u} [Category.{v} C] (T : C ⥤ C)
    {F G : C ⥤ C} {a b : ℕ} (w : a = b) (q : F ≅ G)
    (α : F ⟶ NaturalTransport.power T a) (β : G ⟶ NaturalTransport.power T b)
    (h : HEq (q.hom ≫ β) α) : HEq (q.inv ≫ α) β := by
  subst b
  rw [← eq_of_heq h]
  simp

private theorem trans_heq {C : Type u} [Category.{v} C] (T : C ⥤ C)
    {F G H : C ⥤ C} {a b c : ℕ} (w : a = b) (w' : b = c)
    (q : F ⟶ G) (s : G ⟶ H)
    (α : F ⟶ NaturalTransport.power T a) (β : G ⟶ NaturalTransport.power T b)
    (γ : H ⟶ NaturalTransport.power T c)
    (h : HEq (q ≫ β) α) (h' : HEq (s ≫ γ) β) : HEq ((q ≫ s) ≫ γ) α := by
  subst b
  subst c
  rw [Category.assoc, eq_of_heq h', eq_of_heq h]

private theorem associate_completion {C : Type u} [Category.{v} C]
    (P : ℕ+ → C ⥤ C) (d : ∀ r : ℕ+, P r ≅ NaturalTransport.power (P 1) (r : ℕ))
    (A B D : Expression) :
    HEq ((Functor.associator (D.eval P) (B.eval P) (A.eval P)).inv ≫
      completion P d (.product A (.product B D)))
      (completion P d (.product (.product A B) D)) := by
  have h := merge_assoc (P 1) (completion P d A) (completion P d B) (completion P d D)
  have h' : ((Functor.associator (D.eval P) (B.eval P) (A.eval P)).inv ≫
      completion P d (.product A (.product B D))) ≫
      eqToHom (congrArg (NaturalTransport.power (P 1))
        (Nat.add_assoc A.weight B.weight D.weight).symm) =
      completion P d (.product (.product A B) D) := by
    simpa only [completion, Category.assoc] using h
  exact (comp_eqToHom_heq _ _).symm.trans (heq_of_eq h')

private theorem evaluation_completion {C : Type u} [Category.{v} C]
    (P : ℕ+ → C ⥤ C) (c : ∀ a b : ℕ+, P (a + b) ≅ P b ⋙ P a)
    (d : ∀ r : ℕ+, P r ≅ NaturalTransport.power (P 1) (r : ℕ))
    (hbinary : ∀ a b : ℕ+, d (a + b) = c a b ≪≫
      Functor.isoWhiskerLeft (P b) (d a) ≪≫
      Functor.isoWhiskerRight (d b) (NaturalTransport.power (P 1) (a : ℕ)) ≪≫
      powerProductIso (P 1) (a : ℕ) (b : ℕ))
    {E F : Expression} {q : E.eval P ≅ F.eval P} (h : Evaluation P c E F q) :
    E.weight = F.weight ∧ HEq (q.hom ≫ completion P d F) (completion P d E) := by
  induction h with
  | refl E => exact ⟨rfl, heq_of_eq (Category.id_comp _)⟩
  | split a b =>
    refine ⟨rfl, heq_of_eq ?_⟩
    exact (congrArg Iso.hom (hbinary a b)).symm
  | associate A B D =>
    exact ⟨Nat.add_assoc _ _ _, associate_completion P d A B D⟩
  | unassociate A B D =>
    refine ⟨(Nat.add_assoc _ _ _).symm, ?_⟩
    exact inverse_heq (P 1) (Nat.add_assoc _ _ _)
      (Functor.associator (D.eval P) (B.eval P) (A.eval P)).symm
      _ _ (associate_completion P d A B D)
  | outer h B ih =>
    exact ⟨congrArg (· + B.weight) ih.1,
      merge_outer_heq (P 1) ih.1 _ _ _ (completion P d B) ih.2⟩
  | inner A h ih =>
    exact ⟨congrArg (A.weight + ·) ih.1,
      merge_inner_heq (P 1) ih.1 _ (completion P d A) _ _ ih.2⟩
  | trans h k ih ih' =>
    exact ⟨ih.1.trans ih'.1, trans_heq (P 1) ih.1 ih'.1 _ _ _ _ _ ih.2 ih'.2⟩

private theorem completion_eq_normalize {C : Type u} [Category.{v} C]
    (P : ℕ+ → C ⥤ C) (d : ∀ r : ℕ+, P r ≅ NaturalTransport.power (P 1) (r : ℕ))
    (hd : d 1 = Iso.refl (P 1)) (E : Expression) (h : E.Complete) :
    completion P d E = (E.normalize P h).hom := by
  induction E with
  | atom r =>
    change r = 1 at h
    subst r
    simp [completion, Expression.normalize, Expression.eval, hd, NaturalTransport.power,
      Functor.id_comp]
  | product A B ihA ihB =>
    simp only [completion, merge, ihA h.1, ihB h.2, Expression.normalize,
      Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]

private theorem iso_heq {C : Type u} [Category.{v} C] {F G H : C ⥤ C}
    (w : G = H) (f : F ≅ G) (g : F ≅ H) (h : HEq f.hom g.hom) : HEq f g := by
  subst H
  exact heq_of_eq (Iso.ext (eq_of_heq h))

/-- Every complete ordered refinement evaluates to its prescribed comparison with a power.
`HEq` only accommodates the syntactically different exponent `E.weight` at the endpoint:
refinement preserves weight, so this is equality after the canonical index identification.
The path quantifier includes every parenthesized positive partition followed by complete
refinements, with arbitrary interleavings and intervening reassociations. For one part it
is the same path assertion; for root weight one the path may be empty.

Source: main-20261015 blueprint, sec-trace-formula/sk-d-weil,
lem-trf-frobenius-operator-compact-description.proof.md, categorical expansion of the iterate
assertion (blueprint: lem-trf-positive-functor-refinement-independence).

Proof plan:
1. The powers of def-trf-endofunctor-powers have the prescribed iterated action. All canonical
   reassociations have identity components. Work componentwise using def-nagata-category.
2. Complete any intermediate expression recursively: at a symbol use `d`; at a product
   compose the outer comparison evaluated on the inner functor, then the inner comparison
   mapped by the outer power. Naturality and invertibility follow from those of the factors.
3. Expand both completions for three factors. Functoriality and the power convention give
   the same threefold composite, so completion is invariant under reassociation in contexts.
4. Binary compatibility says a split preserves completion. In an outer context this follows
   by substitution; in an inner context use naturality of the outer completion at the split.
5. Induct along the evaluation path: completion after the partial evaluation is always `d r`.
   At a complete endpoint all leaf completions are identities by `hd`; recursively their
   composite is exactly the canonical normalization. This gives the asserted equality.
6. Grafting complete refinements onto the parts of any positive partition gives such a path.
   Every allowed interleaving is included. One part requires no initial split; at weight one
   the empty composite is the identity, which is `d 1` by `hd`. -/
theorem evaluation_eq_comparison
    {C : Type u} [Category.{v} C] (P : ℕ+ → C ⥤ C)
    (c : ∀ a b : ℕ+, P (a + b) ≅ P b ⋙ P a)
    (d : ∀ r : ℕ+, P r ≅ NaturalTransport.power (P 1) (r : ℕ))
    (hd : d 1 = Iso.refl (P 1))
    (hbinary : ∀ a b : ℕ+, d (a + b) = c a b ≪≫
      Functor.isoWhiskerLeft (P b) (d a) ≪≫
      Functor.isoWhiskerRight (d b) (NaturalTransport.power (P 1) (a : ℕ)) ≪≫
      powerProductIso (P 1) (a : ℕ) (b : ℕ)) :
    ∀ (r : ℕ+) (E : Expression) (q : P r ≅ E.eval P),
      Evaluation P c (.atom r) E q →
      ∀ h : E.Complete, HEq (q ≪≫ E.normalize P h) (d r) := by
  intro r E q h hc
  obtain ⟨w, hq⟩ := evaluation_completion P c d hbinary h
  rw [completion_eq_normalize P d hd E hc] at hq
  change HEq (q.hom ≫ (E.normalize P hc).hom) (d r).hom at hq
  have wp : NaturalTransport.power (P 1) E.weight =
      NaturalTransport.power (P 1) (r : ℕ) := congrArg _ w.symm
  exact iso_heq wp (q ≪≫ E.normalize P hc) (d r) hq

end CategoryTheory.PositiveFunctorRefinement
