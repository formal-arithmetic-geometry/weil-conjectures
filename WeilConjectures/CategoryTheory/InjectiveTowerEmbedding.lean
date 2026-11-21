/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Category.Grp.EnoughInjectives
import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Embedding towers into injective split towers

Source: Stacks Project, More on Algebra, Tag 07KW, Lemma 15.88.1 proof footnote.
-/

@[expose] public section

universe u

open CategoryTheory

namespace CategoryTheory

private noncomputable def embeddingTowerObj (J : ℕ → AddCommGrpCat.{u}) :
    ℕ → AddCommGrpCat.{u}
  | 0 => J 0
  | n + 1 => Limits.prod (embeddingTowerObj J n) (J (n + 1))

private noncomputable def embeddingTowerApp (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    (J : ℕ → AddCommGrpCat.{u}) (j : ∀ n, A.obj (Opposite.op n) ⟶ J n) :
    ∀ n, A.obj (Opposite.op n) ⟶ embeddingTowerObj J n
  | 0 => j 0
  | n + 1 => Limits.prod.lift
      (A.map (homOfLE (Nat.le_add_right n 1)).op ≫ embeddingTowerApp A J j n) (j (n + 1))

/-- Every inverse system of abelian groups embeds in a tower of injective groups with split
surjective transition maps (Stacks Project, Tag 07KW, Lemma 15.88.1 proof footnote).
The index `n : ℕ` denotes the paper's level `n + 1`.
-/
theorem tower_injective_embedding (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :
    ∃ (I : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) (i : A ⟶ I),
      Mono i ∧
        (∀ n : ℕ, Injective (I.obj (Opposite.op n))) ∧
          (∀ n : ℕ,
            IsSplitEpi (I.map (homOfLE (Nat.le_add_right n 1)).op)) := by
  classical
  let J : ℕ → AddCommGrpCat.{u} := fun n ↦ Injective.under (A.obj (Opposite.op n))
  let j : ∀ n, A.obj (Opposite.op n) ⟶ J n := fun n ↦ Injective.ι _
  let p : ∀ n, embeddingTowerObj J (n + 1) ⟶ embeddingTowerObj J n :=
    fun _ ↦ Limits.prod.fst
  let I := Functor.ofOpSequence p
  let i : A ⟶ I := NatTrans.ofOpSequence (embeddingTowerApp A J j) (fun n ↦ by
    dsimp [I, p]
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    exact (Limits.prod.lift_fst _ _).symm)
  refine ⟨I, i, ?_, ?_, ?_⟩
  · have hm : ∀ n, Mono (embeddingTowerApp A J j n) := by
      intro n
      cases n with
      | zero => exact Injective.ι_mono _
      | succ n =>
        have : Mono (j (n + 1)) := Injective.ι_mono _
        exact mono_of_mono_fac (Limits.prod.lift_snd _ _)
    have : ∀ n, Mono (i.app n) := fun n ↦ hm n.unop
    exact NatTrans.mono_of_mono_app i
  · intro n
    change Injective (embeddingTowerObj J n)
    induction n with
    | zero => exact Injective.injective_under _
    | succ n ih =>
      let := ih
      change Injective (Limits.prod (embeddingTowerObj J n) (J (n + 1)))
      infer_instance
  · intro n
    dsimp [I]
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    change IsSplitEpi (Limits.prod.fst : Limits.prod (embeddingTowerObj J n) (J (n + 1)) ⟶ _)
    infer_instance

end CategoryTheory
