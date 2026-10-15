/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.CategoryTheory.IndexedCoveringClass
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Order.RelClasses
import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal

/-!
# A small set of covering families representing a covering class

Source: Stacks Project, Sets, Lemma 000X, clauses (1)-(3)
(blueprint: lem-weil-pbc-small-set-of-covering-families).
-/

@[expose] public section

universe u v w

namespace CategoryTheory.PreZeroHypercover

/-- Source: Stacks Project, Sets, Lemma 000X and Section 000W
(blueprint: lem-weil-pbc-small-set-of-covering-families).

Proof plan:
1. The target/support pairs form a small set. Choose one original covering for each
realized pair; retain the target even when the support is empty.
2. Adjoin the prescribed small collection and singleton isomorphisms. Bound all index
cardinalities and the objects and arrows by an infinite cardinal κ. The finite-list
bound `Cardinal.mk_list_le_max` bounds products and dependent sums of these indices.
3. Choose a limit ordinal θ with cofinality greater than κ, using the successor cardinal
of κ and the dependent-sum bound.
4. By `WellFoundedLT.fix`, close the initial collection transfinitely under indexed
composition and one chosen covering pullback presentation for each family and arrow;
at limit stages take unions. Every stage is small, remains in Cov and has indices
bounded by κ.
5. The union at θ contains the prescribed covers and all singleton isomorphisms and
is closed under the chosen covering pullbacks, since θ is a limit.
6. For composition, `Ordinal.iSup_lt_of_lt_cof` bounds the stages of all inner families;
also include the outer family's stage. The composite is added at the next stage.
The initial representatives give equal presieves at the same target, exactly equality
of arrow supports ignoring repetitions. No closure under arbitrary reindexing or under
all possible pullback presentations is asserted. -/
theorem exists_small_coveringFamilies {C : Type u} [Category.{v} C]
    (Cov : Set (Σ X : C, PreZeroHypercover.{max u v w} X))
    (hCov : IsCoveringClass Cov)
    (Cov₀ : Set (Σ X : C, PreZeroHypercover.{max u v w} X))
    (hsmall : Small.{max u v w} Cov₀) (hsub : Cov₀ ⊆ Cov) :
    ∃ Cov' : Set (Σ X : C, PreZeroHypercover.{max u v w} X),
      Small.{max u v w} Cov' ∧ Cov₀ ⊆ Cov' ∧ Cov' ⊆ Cov ∧ IsCoveringClass Cov' ∧
        ∀ (X : C) (E : PreZeroHypercover.{max u v w} X), ⟨X, E⟩ ∈ Cov →
          ∃ F : PreZeroHypercover.{max u v w} X, ⟨X, F⟩ ∈ Cov' ∧ E.presieve₀ = F.presieve₀ := by
  sorry

end CategoryTheory.PreZeroHypercover
