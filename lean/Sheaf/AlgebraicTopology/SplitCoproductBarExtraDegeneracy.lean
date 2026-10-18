/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q74
-/
module

public import Sheaf.AlgebraicTopology.FixedObjectPushoutCoproduct
public import Mathlib.AlgebraicTopology.ExtraDegeneracy

/-!
# Initial-factor insertion in the split coproduct bar

Source: Dwyer--Kan, *Simplicial localizations of categories*, Proposition 8.2,
proof, printed p.279; the factorwise expansion in the DAG node
(blueprint: lem-coef-split-coproduct-bar-extra-degeneracy).

The bar is specified directly by its coproduct cofans and factorwise operator equations.
All insertion maps are the actual coproduct eliminators. Mapping sets are obtained by
applying the hom-set evaluation functor, with the same objects and operators.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace FixedObject.SplitCoproductBar

/-- Package the displayed `F,A_0,...,A_n,V` inclusions as a Mathlib cofan.
Source: Dwyer--Kan, Proposition 8.2, proof, p.279; DAG proof step 1
(blueprint: lem-coef-split-coproduct-bar-extra-degeneracy). -/
def factorCofan {O : Type u} {F A V T : Category.{v} O} (n : ℕ)
    (f : F ⟶ T) (a : Fin (n + 1) → (A ⟶ T)) (z : V ⟶ T) :
    Cofan (fun i : Fin (n + 1) ⊕ Bool ↦
      Sum.elim (fun _ ↦ A) (fun b ↦ cond b F V) i) :=
  Cofan.mk T (fun i ↦ match i with
    | .inl k => a k
    | .inr true => f
    | .inr false => z)

/-- The degree minus one insertion fixes the `F` and `V` factors.
Source: Dwyer--Kan, Proposition 8.2, proof, p.279; DAG proof step 4
(blueprint: lem-coef-split-coproduct-bar-extra-degeneracy). -/
def initialSection {O : Type u} {F V T : Category.{v} O}
    (cFV : BinaryCofan F V) (hcFV : IsColimit cFV) (f : F ⟶ T) (z : V ⟶ T) :
    cFV.pt ⟶ T :=
  BinaryCofan.IsColimit.desc hcFV f z

/-- Insert an unused `A_0`: the old `A_k` goes to `A_(k+1)`, and `F,V` are fixed.
Source: Dwyer--Kan, Proposition 8.2, proof, p.279; DAG proof steps 1 and 4
(blueprint: lem-coef-split-coproduct-bar-extra-degeneracy). -/
def initialInsertion {O : Type u} {F A V : Category.{v} O}
    (R : SimplicialObject (Category.{v} O))
    (f : ∀ n : ℕ, F ⟶ R.obj (op ⦋n⦌))
    (a : ∀ n : ℕ, Fin (n + 1) → (A ⟶ R.obj (op ⦋n⦌)))
    (z : ∀ n : ℕ, V ⟶ R.obj (op ⦋n⦌))
    (hc : ∀ n : ℕ, IsColimit (factorCofan n (f n) (a n) (z n))) (n : ℕ) :
    R.obj (op ⦋n⦌) ⟶ R.obj (op ⦋n + 1⦌) :=
  Cofan.IsColimit.desc (hc n) (fun i ↦ match i with
    | .inl k => a (n + 1) k.succ
    | .inr true => f (n + 1)
    | .inr false => z (n + 1))

/-- Evaluation on the mapping set between two fixed objects, on objects and functors.
Source: Dwyer--Kan, Sections 1.4(ii), 1.4(iv), and Proposition 8.2, proof, p.279;
DAG proof step 7 (blueprint: lem-coef-split-coproduct-bar-extra-degeneracy). -/
def homSetEvaluation {O : Type u} (x y : O) : Category.{v} O ⥤ Type v where
  obj C := C.Hom x y
  map f := ↾f.map
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The augmented simplicial mapping set, including its actual augmentation target.
Source: Dwyer--Kan, Proposition 8.2, proof, p.279; DAG proof step 7
(blueprint: lem-coef-split-coproduct-bar-extra-degeneracy). -/
def mappingAugmentation {O : Type u}
    (R : SimplicialObject.Augmented (Category.{v} O)) (x y : O) :
    SimplicialObject.Augmented (Type v) :=
  ((SimplicialObject.Augmented.whiskering (Category.{v} O) (Type v)).obj
    (homSetEvaluation x y)).obj R

/-- The initial insertion satisfies all five extra-degeneracy identities, and its
restrictions on every mapping set are Mathlib extra-degeneracy data. The bar is
specified by its actual coproduct cofans and the factorwise operator formulas;
there is no freeness assumption on any factor.

Source: Dwyer--Kan, Proposition 8.2, proof, printed p.279, expanded by the DAG;
Mathlib `ExtraDegeneracy`, fields at lines 72--83
(blueprint: lem-coef-split-coproduct-bar-extra-degeneracy).

Proof:
1. The word quotient gives the coproduct property: a factorwise functor acts on a
word by composing the images of its letters. The category laws preserve every
relation. Every arrow is such a word, so restrictions to the factors determine a
functor uniquely. Finite words and their quotient are small; no normal form or
freeness is needed (def-nagata-category).
2. For an ordinal map alpha:[m]→[n], send label k to the least j with k≤alpha(j),
or to V through v if none exists. These least-index maps compose contravariantly,
including the absorbing V case, and give the identity for the identity ordinal map
(def-weil-pbc-simplicial-set).
3. For the injection omitting i, the least-index rule folds the two adjacent labels,
or applies v at the last face. For a surjection repeating i, it skips label i+1.
The augmentations fix F,V and apply v to every A, so are natural. These are exactly
the factorwise hypotheses, on any coproduct presentation of the stated bar.
4. Coproduct elimination constructs both insertion maps. The composite of the
minus-one insertion with augmentation fixes F,V, hence is the identity. Inserting
then taking face zero shifts each A label back to itself. At degree zero, face one
after insertion sends A through v to V, as does augmentation followed by the
minus-one insertion. Equality on factors proves all three identities.
5. For i≤n, shifting and then folding at i+1 agrees with folding at i and shifting:
labels below i go to k+1, the folded pair to i+1, and later labels to k. For i=n+1,
the last label goes through v on both sides and every other label goes to k+1.
The F,V restrictions are fixed. Coproduct uniqueness proves the fourth family.
6. Inserting after i+1 after the initial shift agrees with first inserting after i:
old k goes to k+1 if k≤i and to k+2 otherwise. Both maps fix F,V, so coproduct
uniqueness proves the fifth family, including n=0.
7. Evaluation on Hom(x,y) preserves identity functors and their composition. Apply
it to the five identities to obtain exactly the five Mathlib `ExtraDegeneracy`
fields (lem-coef-extra-degeneracy-contraction). The resulting maps are precisely
the restrictions of the specified insertions. Empty mapping sets are allowed. -/
theorem split_coproduct_bar_extra_degeneracy {O : Type u}
    (F A V : Category.{v} O) (v : A ⟶ V)
    (cFV : BinaryCofan F V) (hcFV : IsColimit cFV)
    (R : SimplicialObject (Category.{v} O))
    (ε : R ⟶ (SimplicialObject.const (Category.{v} O)).obj cFV.pt)
    (f : ∀ n : ℕ, F ⟶ R.obj (op ⦋n⦌))
    (a : ∀ n : ℕ, Fin (n + 1) → (A ⟶ R.obj (op ⦋n⦌)))
    (z : ∀ n : ℕ, V ⟶ R.obj (op ⦋n⦌))
    (hc : ∀ n : ℕ, IsColimit (factorCofan n (f n) (a n) (z n)))
    (hfaceF : ∀ (n : ℕ) (i : Fin (n + 2)), f (n + 1) ≫ R.δ i = f n)
    (hfaceV : ∀ (n : ℕ) (i : Fin (n + 2)), z (n + 1) ≫ R.δ i = z n)
    (hfaceA : ∀ (n : ℕ) (i k : Fin (n + 2)), a (n + 1) k ≫ R.δ i =
      if h : k.val = n + 1 ∧ i.val = n + 1 then v ≫ z n
      else if h' : k.val ≤ i.val then a n ⟨k.val, by omega⟩
      else a n ⟨k.val - 1, by omega⟩)
    (hdegeneracyF : ∀ (n : ℕ) (i : Fin (n + 1)), f n ≫ R.σ i = f (n + 1))
    (hdegeneracyV : ∀ (n : ℕ) (i : Fin (n + 1)), z n ≫ R.σ i = z (n + 1))
    (hdegeneracyA : ∀ (n : ℕ) (i k : Fin (n + 1)), a n k ≫ R.σ i =
      if k.val ≤ i.val then a (n + 1) k.castSucc else a (n + 1) k.succ)
    (haugmentationF : ∀ n : ℕ, f n ≫ ε.app (op ⦋n⦌) = cFV.inl)
    (haugmentationV : ∀ n : ℕ, z n ≫ ε.app (op ⦋n⦌) = cFV.inr)
    (haugmentationA : ∀ (n : ℕ) (k : Fin (n + 1)),
      a n k ≫ ε.app (op ⦋n⦌) = v ≫ cFV.inr) :
    initialSection cFV hcFV (f 0) (z 0) ≫ ε.app (op ⦋0⦌) = 𝟙 cFV.pt ∧
    (∀ n : ℕ, initialInsertion R f a z hc n ≫ R.δ 0 = 𝟙 (R.obj (op ⦋n⦌))) ∧
    initialInsertion R f a z hc 0 ≫ R.δ 1 =
      ε.app (op ⦋0⦌) ≫ initialSection cFV hcFV (f 0) (z 0) ∧
    (∀ (n : ℕ) (i : Fin (n + 2)),
      initialInsertion R f a z hc (n + 1) ≫ R.δ i.succ =
        R.δ i ≫ initialInsertion R f a z hc n) ∧
    (∀ (n : ℕ) (i : Fin (n + 1)),
      initialInsertion R f a z hc n ≫ R.σ i.succ =
        R.σ i ≫ initialInsertion R f a z hc (n + 1)) ∧
    ∀ x y : O,
      ∃ ed : (mappingAugmentation { left := R, right := cFV.pt, hom := ε } x y).ExtraDegeneracy,
        ed.s' = (homSetEvaluation x y).map (initialSection cFV hcFV (f 0) (z 0)) ∧
        ∀ n : ℕ, ed.s n = (homSetEvaluation x y).map (initialInsertion R f a z hc n) := by
  sorry

end FixedObject.SplitCoproductBar

end
