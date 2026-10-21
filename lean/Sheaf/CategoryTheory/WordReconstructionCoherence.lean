/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Mathlib.Combinatorics.Quiver.Path
public import Mathlib.CategoryTheory.Whiskering

/-! # Word comparisons and reconstruction coherence

Source: blueprint fix-lem-exchanges, Proof Step 5, categorical word-comparison prerequisite
(blueprint: lem-sf-cbc-word-reconstruction-coherence).

Words are Mathlib quiver paths. The helpers give the recursive composites, binary expressions,
and canonical flattening isomorphisms appearing in the statement. All their data are explicit.
The theorem asserts uniqueness, invertibility on the full subcategories, concatenation, and
both flattening equations on the whole source category.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

universe i e u v u' v'

open CategoryTheory.Functor

namespace CategoryTheory.WordReconstruction

variable {S : Type i} [Quiver.{e} S]

/-- The fixed recursive composite of a word, with empty composite the identity.
Source: fix-lem-exchanges Step 5, word notation
(blueprint: lem-sf-cbc-word-reconstruction-coherence). -/
@[implicit_reducible]
def wordFunctor {D : S → Type u} [∀ s, Category.{v} (D s)]
    (F : ∀ {s t : S}, (s ⟶ t) → (D s ⥤ D t)) {s : S} :
    ∀ {t : S}, Quiver.Path s t → (D s ⥤ D t)
  | _, .nil => 𝟭 _
  | _, .cons W f => wordFunctor F W ⋙ F f

/-- The canonical identification of a concatenated word with its two composites.
Source: fix-lem-exchanges Step 5, reassociation and identity removal
(blueprint: lem-sf-cbc-word-reconstruction-coherence). -/
@[implicit_reducible]
def wordCompIso {D : S → Type u} [∀ s, Category.{v} (D s)]
    (F : ∀ {s t : S}, (s ⟶ t) → (D s ⥤ D t)) {s t : S}
    (W : Quiver.Path s t) : ∀ {r : S} (V : Quiver.Path t r),
      wordFunctor F (W.comp V) ≅ wordFunctor F W ⋙ wordFunctor F V
  | _, .nil => (Functor.rightUnitor (wordFunctor F W)).symm
  | _, .cons V f =>
      isoWhiskerRight (wordCompIso F W V) (F f) ≪≫
        Functor.associator (wordFunctor F W) (wordFunctor F V) (F f)

/-- Binary expressions of composable edges, allowing arbitrary empty identity factors.
Source: fix-lem-exchanges Step 5, parenthesization notation
(blueprint: lem-sf-cbc-word-reconstruction-coherence). -/
inductive Expression : S → S → Type (max i e) where
  | empty (s : S) : Expression s s
  | edge {s t : S} (f : s ⟶ t) : Expression s t
  | comp {s t r : S} (A : Expression s t) (B : Expression t r) : Expression s r

/-- The ordered edge word of a binary expression.
Source: fix-lem-exchanges Step 5, flattening notation
(blueprint: lem-sf-cbc-word-reconstruction-coherence). -/
@[implicit_reducible]
def Expression.flatten : ∀ {s t : S}, Expression s t → Quiver.Path s t
  | _, _, .empty _ => .nil
  | _, _, .edge f => Quiver.Hom.toPath f
  | _, _, .comp A B => A.flatten.comp B.flatten

/-- Evaluate a binary expression without changing its parentheses or empty factors.
Source: fix-lem-exchanges Step 5, expression functors
(blueprint: lem-sf-cbc-word-reconstruction-coherence). -/
@[implicit_reducible]
def Expression.functor {D : S → Type u} [∀ s, Category.{v} (D s)]
    (F : ∀ {s t : S}, (s ⟶ t) → (D s ⥤ D t)) :
    ∀ {s t : S}, Expression s t → (D s ⥤ D t)
  | _, _, .empty _ => 𝟭 _
  | _, _, .edge f => F f
  | _, _, .comp A B => A.functor F ⋙ B.functor F

/-- Canonical flattening built solely from functor associators and unitors.
Source: fix-lem-exchanges Step 5, the maps c_E and d_E
(blueprint: lem-sf-cbc-word-reconstruction-coherence). -/
@[implicit_reducible]
def Expression.flattenIso {D : S → Type u} [∀ s, Category.{v} (D s)]
    (F : ∀ {s t : S}, (s ⟶ t) → (D s ⥤ D t)) :
    ∀ {s t : S} (E : Expression s t), wordFunctor F E.flatten ≅ E.functor F
  | _, _, .empty _ => Iso.refl _
  | _, _, .edge f => Functor.leftUnitor (F f)
  | _, _, .comp A B =>
      wordCompIso F A.flatten B.flatten ≪≫
        isoWhiskerRight (A.flattenIso F) (wordFunctor F B.flatten) ≪≫
          isoWhiskerLeft (A.functor F) (B.flattenIso F)

variable {D : S → Type u} {T : S → Type u'}
    [∀ s, Category.{v} (D s)] [∀ s, Category.{v'} (T s)]
    (R : ∀ s, D s ⥤ T s)
    (F : ∀ {s t : S}, (s ⟶ t) → (D s ⥤ D t))
    (G : ∀ {s t : S}, (s ⟶ t) → (T s ⥤ T t))
    (qEdge : ∀ {s t : S} (f : s ⟶ t), F f ⋙ R t ⟶ R s ⋙ G f)

/-- The recursive expression comparison from the supplied edge and identity maps.
Source: fix-lem-exchanges Step 5, q_E
(blueprint: lem-sf-cbc-word-reconstruction-coherence). -/
@[implicit_reducible]
def Expression.comparison
    (qEdge : ∀ {s t : S} (f : s ⟶ t), F f ⋙ R t ⟶ R s ⋙ G f) : ∀ {s t : S} (E : Expression s t),
    E.functor F ⋙ R t ⟶ R s ⋙ E.functor G
  | _, _, .empty s => 𝟙 (R s)
  | _, _, .edge f => qEdge f
  | _, _, .comp A B =>
      whiskerLeft (A.functor F) (Expression.comparison qEdge B) ≫
        whiskerRight (Expression.comparison qEdge A) (B.functor G)

/-- The empty, edge, and recursive equations for a family of word comparisons.
Source: fix-lem-exchanges Step 5, the defining equations for q_W
(blueprint: lem-sf-cbc-word-reconstruction-coherence). -/
@[implicit_reducible]
def IsWordComparison
    (qEdge : ∀ {s t : S} (f : s ⟶ t), F f ⋙ R t ⟶ R s ⋙ G f)
    (q : ∀ {s t : S} (W : Quiver.Path s t),
      wordFunctor F W ⋙ R t ⟶ R s ⋙ wordFunctor G W) : Prop :=
  (∀ s : S, q (.nil : Quiver.Path s s) = 𝟙 (R s)) ∧
  (∀ {s t : S} (f : s ⟶ t), q (Quiver.Hom.toPath f) = qEdge f) ∧
  (∀ {s t r : S} (W : Quiver.Path s t) (f : t ⟶ r),
    q (W.cons f) = whiskerLeft (wordFunctor F W) (qEdge f) ≫ whiskerRight (q W) (G f))

/-- Reconstruct a comparison by first applying the given unit and then L(q).
Source: fix-lem-exchanges Step 5, a_W and a_E
(blueprint: lem-sf-cbc-word-reconstruction-coherence). -/
@[implicit_reducible]
def reconstruct (L : ∀ s, T s ⥤ D s) (η : ∀ s, 𝟭 (D s) ⟶ R s ⋙ L s)
    {s t : S} (A : D s ⥤ D t) (B : T s ⥤ T t) (q : A ⋙ R t ⟶ R s ⋙ B) :
    A ⟶ (R s ⋙ B) ⋙ L t :=
  whiskerLeft A (η t) ≫ whiskerRight q (L t)

private def wordComparison
    (qEdge : ∀ {s t : S} (f : s ⟶ t), F f ⋙ R t ⟶ R s ⋙ G f) {s : S} :
    ∀ {t : S} (W : Quiver.Path s t),
    wordFunctor F W ⋙ R t ⟶ R s ⋙ wordFunctor G W
  | _, .nil => 𝟙 (R s)
  | _, .cons W f =>
      whiskerLeft (wordFunctor F W) (qEdge f) ≫
        whiskerRight (wordComparison qEdge W) (G f)

/-- Supplied generator comparisons extend uniquely to words, and reconstruction respects
concatenation, all binary parentheses, and arbitrary empty factors.
Source: fix-lem-exchanges Proof Step 5, categorical prerequisite
(blueprint: lem-sf-cbc-word-reconstruction-coherence).

Proof:
1. Functor associators and unitors have identity components. Their composites and
   whiskerings construct the canonical word and expression flattenings.
2. Define q on empty words by identity, and on W followed by f by
   whiskerLeft F_W q_f followed by whiskerRight q_W G_f. Naturality follows from
   the naturality of each factor, or componentwise from functoriality and q_f's square.
3. The singleton equation follows from preservation of identities; induction on word
   length makes every other family satisfying these equations equal to q.
4. Induct on word length for preservation of E and invertibility of q_W(x).
   In the step the inverse is G_f(q_W(x) inverse) followed by q_f(F_W x) inverse.
   These component inverses are natural on the full subcategory, by the naturality
   equation multiplied by its invertible components.
5. The reconstruction is natural as a composite of whiskerings. On E its factors
   are invertible by step 4 and the unit hypothesis, so it too restricts to an
   isomorphism. The empty reconstruction is eta by preservation of identities.
6. Induct on the second word V for the concatenation equation, expanding the recursion
   and using preservation of composition and associativity. Insert wordCompIso.
7. Induct on the binary expression. Use the two inductive equations, the defining
   expression composite, and step 6 to get the q flattening equation, including
   empty children and empty expressions of arbitrary finite depth.
8. Apply L to step 7 and compose with eta. The naturality exchange law
   lem-amb-natural-transformation-whisker-exchange moves eta across c_E and gives
   the reconstruction flattening equation. Both equations hold on all of D_s;
   no faithfulness or adjunction is used.
-/
theorem word_reconstruction_coherence
    (E : ∀ s, D s → Prop) (L : ∀ s, T s ⥤ D s)
    (η : ∀ s, 𝟭 (D s) ⟶ R s ⋙ L s)
    (hη : ∀ (s : S) (x : D s), E s x → IsIso ((η s).app x))
    (hF : ∀ {s t : S} (f : s ⟶ t) (x : D s), E s x → E t ((F f).obj x))
    (hq : ∀ {s t : S} (f : s ⟶ t) (x : D s), E s x → IsIso ((qEdge f).app x)) :
    ∃ q : ∀ {s t : S} (W : Quiver.Path s t),
        wordFunctor F W ⋙ R t ⟶ R s ⋙ wordFunctor G W,
      IsWordComparison R F G qEdge q ∧
      (∀ q' : ∀ {s t : S} (W : Quiver.Path s t),
          wordFunctor F W ⋙ R t ⟶ R s ⋙ wordFunctor G W,
        IsWordComparison R F G qEdge q' → @q' = @q) ∧
      (∀ {s t : S} (W : Quiver.Path s t) (x : D s), E s x →
        E t ((wordFunctor F W).obj x) ∧ IsIso ((q W).app x) ∧
          IsIso ((reconstruct R L η (wordFunctor F W) (wordFunctor G W) (q W)).app x)) ∧
      (∀ {s t r : S} (W : Quiver.Path s t) (V : Quiver.Path t r),
        q (W.comp V) ≫ whiskerLeft (R s) (wordCompIso G W V).hom =
          whiskerRight (wordCompIso F W V).hom (R r) ≫
            whiskerLeft (wordFunctor F W) (q V) ≫ whiskerRight (q W) (wordFunctor G V)) ∧
      (∀ s : S, reconstruct R L η (𝟭 (D s)) (𝟭 (T s))
          (q (.nil : Quiver.Path s s)) = η s) ∧
      (∀ {s t : S} (A : Expression s t),
        (q A.flatten ≫ whiskerLeft (R s) (A.flattenIso G).hom =
          whiskerRight (A.flattenIso F).hom (R t) ≫ Expression.comparison R F G qEdge A) ∧
        (reconstruct R L η (wordFunctor F A.flatten) (wordFunctor G A.flatten)
            (q A.flatten) ≫ whiskerRight (whiskerLeft (R s) (A.flattenIso G).hom) (L t) =
          (A.flattenIso F).hom ≫
            reconstruct R L η (A.functor F) (A.functor G)
              (Expression.comparison R F G qEdge A))) := by
  let q {s t : S} (W : Quiver.Path s t) := wordComparison R F G qEdge W
  have hnil (s : S) : q (.nil : Quiver.Path s s) = 𝟙 (R s) := rfl
  have hcons {s t r : S} (W : Quiver.Path s t) (f : t ⟶ r) :
      q (W.cons f) =
        whiskerLeft (wordFunctor F W) (qEdge f) ≫ whiskerRight (q W) (G f) := rfl
  have hedge {s t : S} (f : s ⟶ t) : q (Quiver.Hom.toPath f) = qEdge f := by
    ext x
    simp [Quiver.Hom.toPath, hcons, hnil, wordFunctor]
  have hword : IsWordComparison R F G qEdge q := ⟨hnil, hedge, hcons⟩
  -- Keep the prescribed concatenation isomorphisms explicit in the induction.
  have hcomp {s t r : S} (W : Quiver.Path s t) (V : Quiver.Path t r) :
      q (W.comp V) ≫ whiskerLeft (R s) (wordCompIso G W V).hom =
        whiskerRight (wordCompIso F W V).hom (R r) ≫
          whiskerLeft (wordFunctor F W) (q V) ≫ whiskerRight (q W) (wordFunctor G V) := by
    induction V with
    | nil =>
        ext x
        simp [wordCompIso, hnil, wordFunctor]
    | @cons r r' V f ih =>
        ext x
        have hi := congrArg (fun α => α.app x) ih
        simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] at hi ⊢
        simp only [Functor.comp_obj, Quiver.Path.comp_cons, wordFunctor, hcons,
          NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, wordCompIso,
          Iso.trans_hom, isoWhiskerRight_hom, associator_hom_app, Category.comp_id,
          Category.assoc, Functor.comp_map] at hi ⊢
        have hn := (qEdge f).naturality ((wordCompIso F W V).hom.app x)
        simp only [Functor.comp_map] at hn
        rw [← Functor.map_comp, hi]
        simp only [Functor.map_comp]
        rw [← Category.assoc, ← hn, Category.assoc]
        rfl
  refine ⟨q, hword, ?_, ?_, hcomp, ?_, ?_⟩
  · intro q' hq'
    funext s t W
    induction W with
    | nil => exact (hq'.1 s).trans (hnil s).symm
    | cons W f ih =>
        exact (hq'.2.2 W f).trans
          ((congrArg (fun a => whiskerLeft (wordFunctor F W) (qEdge f) ≫
            whiskerRight a (G f)) ih).trans (hcons W f).symm)
  · intro s t W x hx
    have hi : E t ((wordFunctor F W).obj x) ∧ IsIso ((q W).app x) := by
      induction W with
      | nil =>
          simpa [wordFunctor, hnil] using
            And.intro hx (inferInstance : IsIso (𝟙 ((R s).obj x)))
      | cons W f ih =>
          have := hq f ((wordFunctor F W).obj x) ih.1
          have := ih.2
          refine ⟨hF f _ ih.1, ?_⟩
          simpa only [hcons, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] using
            (inferInstance : IsIso ((qEdge f).app ((wordFunctor F W).obj x) ≫
              (G f).map ((q W).app x)))
    refine ⟨hi.1, hi.2, ?_⟩
    have := hη t _ hi.1
    have := hi.2
    dsimp [reconstruct]
    infer_instance
  · intro s
    ext x
    simp [reconstruct, hnil]
  · intro s t A
    have hflat : q A.flatten ≫ whiskerLeft (R s) (A.flattenIso G).hom =
        whiskerRight (A.flattenIso F).hom (R t) ≫ Expression.comparison R F G qEdge A := by
      induction A with
      | empty s =>
          ext x
          simp [Expression.flatten, Expression.flattenIso, Expression.comparison, hnil]
      | edge f =>
          ext x
          simp [Expression.flatten, Expression.flattenIso, Expression.comparison,
            Quiver.Hom.toPath, hcons, hnil, wordFunctor]
      | @comp s t r A B ihA ihB =>
          ext x
          have hc := congrArg (fun α => α.app x) (hcomp A.flatten B.flatten)
          have ha := congrArg (fun α => α.app x) ihA
          have hb := congrArg (fun α => α.app ((A.functor F).obj x)) ihB
          simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] at hc ha hb
          simp only [Expression.flatten, Expression.flattenIso, Expression.comparison,
            Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom,
            NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, Functor.map_comp,
            Functor.comp_obj, Category.assoc]
          rw [reassoc_of% hc, ← Functor.map_comp_assoc, ha, Functor.map_comp_assoc]
          -- Move the two flattening components through the comparison square.
          have hn := (q B.flatten).naturality ((A.flattenIso F).hom.app x)
          simp only [Functor.comp_map] at hn
          rw [← reassoc_of% hn]
          have hd := (B.flattenIso G).hom.naturality
            ((Expression.comparison R F G qEdge A).app x)
          simp only [Functor.comp_obj] at hd
          rw [hd, reassoc_of% hb]
    refine ⟨hflat, ?_⟩
    ext x
    -- Reconstruction follows by applying L and using naturality of the unit.
    have hi := congrArg (fun α => (L t).map (α.app x)) hflat
    simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, Functor.map_comp] at hi
    dsimp [reconstruct]
    rw [Category.assoc, hi, ← Category.assoc]
    have hn := (η t).naturality ((A.flattenIso F).hom.app x)
    simp only [Functor.id_map, Functor.comp_map] at hn
    rw [← hn, Category.assoc]

end CategoryTheory.WordReconstruction
