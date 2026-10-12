/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Category.Preorder
public import Sheaf.CategoryTheory.Limits.TowerTransitionEndomorphism

/-!
# Positive right derived limits of towers

Source: Stacks Project, More on Algebra, Tag 07KW, Lemma 15.88.1.
(blueprint: lem-pc-roos-positive-derived-limit).
-/

@[expose] public section

universe u

namespace CategoryTheory

open Limits

/-- Positive-degree Roos computation, including naturality of the degree-one
identification. The tower category and additive limit instances are explicit
parameters; no left-exactness or kernel identification is asserted here.

Source: Stacks Project, More on Algebra, Tag 07KW, Lemma 15.88.1.
(blueprint: lem-pc-roos-positive-derived-limit).

Proof: Reindex the source's positive indices by n+1. For A form the finite-product
systems B_n = A_n × ... × A_0 and C_n = A_(n-1) × ... × A_0, with C_0 = 0 and
projection transitions. Embed A_n into B_n by all successive transition maps.
Send B_n to C_n by x_i - f_i(x_(i+1)). The maps commute with transitions.
The first map is injective by its last-index coordinate. Its image is the kernel
of the second because the equations determine every coordinate from x_n. The
second is surjective: set x_n=0 and solve downwards x_i=y_i+f_i(x_(i+1)). Thus
0 → A → B → C → 0 is short exact, levelwise and in the functor category.
Both B and C have surjective transitions, hence all their positive derived limits
vanish by Tag 07KW(3). Their limits identify with the full product of the A_n,
and the map on limits identifies with one minus the transition shift. The long
exact sequence therefore makes its connecting map an epimorphism with kernel
the image of this endomorphism. The cokernel universal property gives the
stated degree-one isomorphism. For q≥2 both adjacent
terms R^(q-1)lim C and R^q lim B vanish, so exactness implies R^q lim A=0.
Morphisms act coordinatewise on B and C. Naturality of the connecting morphism
and uniqueness in the cokernel universal property give the stated square.
All chosen isomorphisms are the uniquely determined factorisations of these
canonical maps. The zero tower and constant towers satisfy the same argument. -/
theorem roosPositiveDerivedLimit
    [EnoughInjectives (ℕᵒᵖ ⥤ AddCommGrpCat.{u})]
    [(lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).Additive] :
    ∃ (e₁ : ∀ A : ℕᵒᵖ ⥤ AddCommGrpCat.{u},
        ((lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).rightDerived 1).obj A ≅
          cokernel ((towerTransitionEndomorphism
            (K := fun n : ℕ => A.obj (Opposite.op n))
            (fun n => A.map (homOfLE (Nat.le_succ n)).op)))),
      (∀ (A B : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) (φ : A ⟶ B),
        ∃ h : (towerTransitionEndomorphism
            (K := fun n : ℕ => A.obj (Opposite.op n))
            (fun n => A.map (homOfLE (Nat.le_succ n)).op)) ≫
            Limits.Pi.map (fun n : ℕ => φ.app (Opposite.op n)) =
            Limits.Pi.map (fun n : ℕ => φ.app (Opposite.op n)) ≫ (towerTransitionEndomorphism
            (K := fun n : ℕ => B.obj (Opposite.op n))
            (fun n => B.map (homOfLE (Nat.le_succ n)).op)),
          ((lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).rightDerived 1).map φ ≫
              (e₁ B).hom = (e₁ A).hom ≫
            cokernel.map ((towerTransitionEndomorphism
            (K := fun n : ℕ => A.obj (Opposite.op n))
            (fun n => A.map (homOfLE (Nat.le_succ n)).op))) ((towerTransitionEndomorphism
            (K := fun n : ℕ => B.obj (Opposite.op n))
            (fun n => B.map (homOfLE (Nat.le_succ n)).op)))
              (Limits.Pi.map (fun n : ℕ => φ.app (Opposite.op n)))
              (Limits.Pi.map (fun n : ℕ => φ.app (Opposite.op n))) h) ∧
      ∀ (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) (q : ℕ), 2 ≤ q →
        IsZero (((lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).rightDerived q).obj A) := by
  sorry

end CategoryTheory
