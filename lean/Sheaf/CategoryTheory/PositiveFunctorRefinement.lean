/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import Sheaf.CategoryTheory.NaturalTransportInduction
public import Mathlib.Data.PNat.Basic

/-! # Ordered positive functor expressions and refinement evaluations

Source: main-20261015 blueprint, sec-trace-formula/sk-d-weil,
lem-trf-frobenius-operator-compact-description.proof.md, categorical expansion of the iterate
assertion; Stacks 001I, 003E and 003F for natural transformations and their compositions.
(blueprint: def-trf-positive-functor-refinement)
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.PositiveFunctorRefinement

/-- Parenthesized nonempty words in positively weighted functor symbols, in functional order.
Source: categorical expansion of the blueprint's iterate assertion
(blueprint: def-trf-positive-functor-refinement). -/
inductive Expression : Type where
  | atom (r : ℕ+) : Expression
  | product (A B : Expression) : Expression

/-- Total weight of an ordered expression.
Source: the ordered splitting trees in the blueprint's iterate assertion
(blueprint: def-trf-positive-functor-refinement). -/
def Expression.weight : Expression → ℕ
  | .atom r => r
  | .product A B => A.weight + B.weight

/-- Interpret a product `A B` as the functional composite `A ∘ B`.
Source: the ordered splitting trees in the blueprint's iterate assertion
(blueprint: def-trf-positive-functor-refinement). -/
def Expression.eval {C : Type u} [Category.{v} C] (P : ℕ+ → C ⥤ C) :
    Expression → C ⥤ C
  | .atom r => P r
  | .product A B => B.eval P ⋙ A.eval P

/-- An expression is complete precisely when every leaf has weight one.
Source: complete ordered splitting trees in the blueprint's iterate assertion
(blueprint: def-trf-positive-functor-refinement). -/
def Expression.Complete : Expression → Prop
  | .atom r => r = 1
  | .product A B => A.Complete ∧ B.Complete

/-- Flatten two functor powers using only associators, unitors and index equality transports.
Its components are identity maps on the iterated object, so it is the prescribed canonical
identification. The argument order is functional: the outer exponent is `a`.
Source: the power convention of the blueprint's iterate assertion; Stacks 003F
(blueprint: def-trf-positive-functor-refinement). -/
def powerProductIso {C : Type u} [Category.{v} C] (T : C ⥤ C) :
    (a b : ℕ) → NaturalTransport.power T b ⋙ NaturalTransport.power T a ≅
      NaturalTransport.power T (a + b)
  | 0, b => Functor.rightUnitor (NaturalTransport.power T b) ≪≫
      eqToIso (congrArg (NaturalTransport.power T) (Nat.zero_add b).symm)
  | a + 1, b =>
    (Functor.associator _ _ T).symm ≪≫
      Functor.isoWhiskerRight (powerProductIso T a b) T ≪≫
      eqToIso (congrArg (NaturalTransport.power T) (Nat.succ_add a b).symm)

/-- Canonically identify a complete expression with the power given by its total weight.
At a leaf use its equality with weight one; at a product whisker the two recursively
constructed identifications and flatten powers. No comparisons `d` are used here.
Source: the leaf identification in the blueprint's iterate assertion
(blueprint: def-trf-positive-functor-refinement). -/
def Expression.normalize {C : Type u} [Category.{v} C] (P : ℕ+ → C ⥤ C) :
    (E : Expression) → E.Complete → (E.eval P ≅ NaturalTransport.power (P 1) E.weight)
  | .atom _r, h => eqToIso (congrArg P h) ≪≫
      (eqToIso (congrArg (fun n : ℕ+ ↦ NaturalTransport.power (P 1) (n : ℕ)) h)).symm
  | .product A B, h =>
    Functor.isoWhiskerLeft (B.eval P) (A.normalize P h.1) ≪≫
      Functor.isoWhiskerRight (B.normalize P h.2) (NaturalTransport.power (P 1) A.weight) ≪≫
      powerProductIso (P 1) A.weight B.weight

/-- The relation of being an evaluation of an ordered refinement path. A split replaces
one symbol by its two ordered positive parts. Associators in either direction and both
functor contexts are allowed. Reflexivity and transitivity allow all finite schedules.
A child can only be split after its parent has created it; independent children may be
processed in either order. The isomorphism index is the actual evaluated composite.
Source: the arbitrary refinement schedules in the blueprint's iterate assertion;
Stacks 001I, 003E and 003F
(blueprint: def-trf-positive-functor-refinement). -/
inductive Evaluation {C : Type u} [Category.{v} C] (P : ℕ+ → C ⥤ C)
    (c : ∀ a b : ℕ+, P (a + b) ≅ P b ⋙ P a) :
    (E F : Expression) → (E.eval P ≅ F.eval P) → Prop where
  | refl (E : Expression) : Evaluation P c E E (Iso.refl _)
  | split (a b : ℕ+) :
      Evaluation P c (.atom (a + b)) (.product (.atom a) (.atom b)) (c a b)
  | associate (A B D : Expression) :
      Evaluation P c (.product (.product A B) D) (.product A (.product B D))
        (Functor.associator (D.eval P) (B.eval P) (A.eval P)).symm
  | unassociate (A B D : Expression) :
      Evaluation P c (.product A (.product B D)) (.product (.product A B) D)
        (Functor.associator (D.eval P) (B.eval P) (A.eval P))
  | outer {E F : Expression} {q : E.eval P ≅ F.eval P}
      (h : Evaluation P c E F q) (B : Expression) :
      Evaluation P c (.product E B) (.product F B) (Functor.isoWhiskerLeft (B.eval P) q)
  | inner (A : Expression) {E F : Expression} {q : E.eval P ≅ F.eval P}
      (h : Evaluation P c E F q) :
      Evaluation P c (.product A E) (.product A F) (Functor.isoWhiskerRight q (A.eval P))
  | trans {E F G : Expression} {q : E.eval P ≅ F.eval P} {s : F.eval P ≅ G.eval P}
      (h : Evaluation P c E F q) (k : Evaluation P c F G s) :
      Evaluation P c E G (q ≪≫ s)

end CategoryTheory.PositiveFunctorRefinement
