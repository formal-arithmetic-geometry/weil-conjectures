/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Sheaf.CategoryTheory.Limits.TowerTransitionEndomorphism

/-!
# The functorial acyclic resolution of a tower

The finite-prefix construction of Stacks Project, Tag 07KW, Lemma 15.88.1.
(blueprint: lem-pc-roos-functorial-acyclic-resolution).
-/

@[expose] public section

universe u

namespace CategoryTheory

open Limits

/-- The product of all levels of a tower, with componentwise maps. -/
noncomputable def roosProductFunctor :
    (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u} where
  obj A := ∏ᶜ fun n : ℕ ↦ A.obj (Opposite.op n)
  map φ := Limits.Pi.map (fun n : ℕ ↦ φ.app (Opposite.op n))
  map_id A := by
    apply Pi.hom_ext
    intro n
    simp
  map_comp φ ψ := by
    apply Pi.hom_ext
    intro n
    simp

/-- The natural endomorphism `1 - shift` of the levelwise product functor. -/
noncomputable def roosProductDifferential :
    roosProductFunctor.{u} ⟶ roosProductFunctor.{u} where
  app A := towerTransitionEndomorphism
    (fun n ↦ A.map (homOfLE (Nat.le_succ n)).op)
  naturality _ _ φ := by
    dsimp only [roosProductFunctor]
    exact towerTransitionEndomorphism_natural_backward _ _ _
      (fun n ↦ (φ.naturality (homOfLE (Nat.le_succ n)).op).symm)

/-- Finite-prefix towers give a functorial length-one limit-acyclic resolution.

Source: Stacks Project, More on Algebra, Tag 07KW, Lemma 15.88.1, proof.
(blueprint: lem-pc-roos-functorial-acyclic-resolution).

Proof: for a tower A indexed starting at zero, put U(A)_n = product of A_i for
0 <= i <= n, and V(A)_n = product of A_i for 0 <= i < n. Transitions forget
the last coordinate. Send a in A_n to its successive transitions in every A_i.
Send (x_i) in U(A)_n to (x_i - f_i(x_(i+1))) for i < n. These maps commute
with transitions. The first is injective by coordinate n. The kernel of the
second consists of successive-transition tuples. The second is surjective:
set x_n = 0 and solve downwards x_i = y_i + f_i(x_(i+1)). Thus the sequence
is levelwise short exact, hence short exact in the abelian functor category.
Apply tower morphisms coordinatewise to obtain functors U,V and natural maps.
Compatible finite prefixes identify each of lim U(A), lim V(A) with the full
product, naturally in A; the induced map is exactly 1 - shift. Both towers
have surjective transitions, so their positive derived limits vanish by
lem-pc-tower-surjective-lim-acyclic (Tag 07KW (3)). The empty prefix at n=0
is the zero group, so the construction also works at the initial index. -/
theorem exists_roos_acyclic_resolution
    [EnoughInjectives (ℕᵒᵖ ⥤ AddCommGrpCat.{u})]
    [(lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).Additive] :
    ∃ (U V : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ (ℕᵒᵖ ⥤ AddCommGrpCat.{u}))
      (i : 𝟭 (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⟶ U) (p : U ⟶ V)
      (w : ∀ A, i.app A ≫ p.app A = 0),
      (∀ A, (ShortComplex.mk (i.app A) (p.app A) (w A)).ShortExact) ∧
      ∃ (eU : U ⋙ lim ≅ roosProductFunctor) (eV : V ⋙ lim ≅ roosProductFunctor),
        (∀ A, lim.map (p.app A) ≫ eV.hom.app A =
          eU.hom.app A ≫ roosProductDifferential.app A) ∧
        ∀ (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) (q : ℕ), 1 ≤ q →
          IsZero ((lim.rightDerived q).obj (U.obj A)) ∧
          IsZero ((lim.rightDerived q).obj (V.obj A)) := by
  sorry

end CategoryTheory
