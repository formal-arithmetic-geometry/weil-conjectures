/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteSplitReplacementStage

/-! Local conditions on finite split replacement stages. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

/-- Each retained term has a finite coproduct presentation whose constituent maps
belong to the prescribed sieve. Source: Stacks, Hypercoverings, 01GJ and 01GK.
(blueprint: def-weil-pbc-finite-split-local-replacement-stage) -/
def StageSolves {X : Scheme.{u}} (K : SimplicialObject X.Etale)
    (S : ∀ n : ℕ, Sieve (K.obj (op (SimplexCategory.mk n))))
    {n : ℕ} (A : FiniteSplitReplacementStage K n) : Prop :=
  ∀ q : Fin (n + 1), ∃ (l : ℕ) (T : Fin l → X.Etale)
    (ι : ∀ i, T i ⟶ A.U.simplicial.obj
      (op ⟨SimplexCategory.mk q.val, Nat.le_of_lt_succ q.isLt⟩)),
    Nonempty (IsColimit (Cofan.mk _ ι)) ∧
      ∀ i, S q.val (ι i ≫ A.f.app
        (op ⟨SimplexCategory.mk q.val, Nat.le_of_lt_succ q.isLt⟩))

end AlgebraicGeometry.FiniteSplitEtaleHypercover
