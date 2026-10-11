/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Embedding towers into injective split towers

Source: Stacks Project, More on Algebra, Tag 07KW, Lemma 15.88.1 proof footnote
(blueprint: lem-pc-tower-injective-embedding).
-/

universe u

open CategoryTheory

namespace CategoryTheory

/-- Every inverse system of abelian groups embeds in a tower of injective groups with split
surjective transition maps (Stacks Project, Tag 07KW, Lemma 15.88.1 proof footnote).
The index `n : ℕ` denotes the paper's level `n + 1`.

Proof (node step 1): apply `lem-weil-pbc-ring-modules-enough-injectives` levelwise with
`R = ℤ` to obtain injective groups `J_n` and monomorphisms `j_n : A_n ⟶ J_n`.
Proof (node step 2): set `I_1 = J_1`, `i_1 = j_1`, and recursively `I_{n+1} = I_n ⊕ J_{n+1}`
with the first projection as transition map and `i_{n+1}(a) = (i_n (f_n a), j_{n+1} a)`.
Finite direct sums preserve injectivity, the projections are split by the summand inclusions,
and the defining formula makes the `i_n` a morphism of towers.
Proof (node step 3): each `i_n` is injective by its two coordinates, and a tower morphism with
injective components is a monomorphism of towers since composition is componentwise.
(blueprint: lem-pc-tower-injective-embedding) -/
theorem tower_injective_embedding (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :
    ∃ (I : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) (i : A ⟶ I),
      Mono i ∧
        (∀ n : ℕ, Injective (I.obj (Opposite.op n))) ∧
          (∀ n : ℕ,
            IsSplitEpi (I.map (homOfLE (Nat.le_add_right n 1)).op)) := by
  sorry

end CategoryTheory
