/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Structural cycle-pullback construction

This is the recursive construction step of Stacks Project, Derived Categories, Lemma 05T7 (1).
The degreewise comparison records the defining kernel-pullback geometry,
without asserting the generalized-element lifting consequence.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Without any epimorphism assumption, the descending construction identifies each term
at or below the bound with T of the pullback of F and the next cycles. The cover followed
by the pullback projections defines its augmentation and differential.

Source: Stacks Project, Derived Categories, Lemma 05T7 (1), and Cohomology on Sites,
Lemma 06YS (blueprint: lem-pc-functorial-cycle-pullback-core-stage3).

Proof: For degrees above N put E equal to zero. Descend through degrees N-k. Having
constructed the next two terms, form the kernel of the next differential and its map
via the next augmentation to F in the next degree. Pull back this map along the
current differential of F, and apply T to that pullback. The map pi to the pullback
defines the comparison. Its first projection is the augmentation; its second projection followed
by the kernel inclusion is the differential. The kernel equation gives differential
square zero, and the pullback equation gives the augmentation chain-map equation.
The terms satisfy S by hT, and above N by hzero. The identification of the current
term with T of the pullback is definitional at its construction stage; assembling
the integer-indexed complex transports it to an isomorphism with both projection
equations. No epimorphism assumption is needed for this construction. For a map F to G,
descending induction induces the kernel maps and then the pullback maps; applying T
produces the term maps. Naturality of pi gives both compatibility equations.
Uniqueness of the induced kernel and pullback maps, together with the identity and
composition laws of T, proves the functor laws and naturality of the augmentation.
This yields Q, epsilon, and the stated identifications at or below the bound. -/
theorem exists_functorial_cyclePullback_core {A : Type u} [Category.{v} A] [Abelian A]
    (S : ObjectProperty A) (hzero : ∀ X : A, IsZero X → S X) (T : A ⥤ A)
    (π : T ⟶ 𝟭 A) (hT : ∀ X : A, S (T.obj X))
    (N : ℤ) :
    let P : ObjectProperty (CochainComplex A ℤ) :=
      fun F ↦ ∀ i : ℤ, N < i → IsZero (F.X i)
    ∃ Q : P.FullSubcategory ⥤ CochainComplex A ℤ, ∃ ε : Q ⟶ P.ι,
      ∀ F : P.FullSubcategory,
        (∀ i : ℤ, S ((Q.obj F).X i)) ∧
        (∀ i : ℤ, N < i → IsZero ((Q.obj F).X i)) ∧
        ∀ (i : ℤ), i ≤ N →
          let d := (Q.obj F).d (i + 1) (i + 1 + 1)
          let f := F.obj.d i (i + 1)
          let g := kernel.ι d ≫ (ε.app F).f (i + 1)
          ∃ (c : (Q.obj F).X i ≅ T.obj (pullback f g)),
            c.hom ≫ π.app (pullback f g) ≫ pullback.fst f g = (ε.app F).f i ∧
            c.hom ≫ π.app (pullback f g) ≫ pullback.snd f g ≫ kernel.ι d =
              (Q.obj F).d i (i + 1) := by sorry

end CochainComplex
