/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.Topology.AbelianOpenExtensionByZero

/-! # Inclusion between constant integer extensions on nested opens

Source: Stacks Project, Cohomology, Lemma 0A38, final paragraph; Sheaves, Lemma 00A5
(blueprint: lem-sc-abelian-integer-open-inclusion).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

/-- The nested-open inclusion is the identity on stalks inside the smaller open.

Source: Stacks Project, Cohomology, Lemma 0A38, final paragraph, and Sheaves, Lemma 00A5.
Proof: identify both extensions with the sheafifications of the slice extension
presheaves of the constant integer sheaf C on X, using the constant-integer open-extension
comparison. Over an open W, the presheaf map sends the summand indexed by W → V to the
summand indexed by the composite W → V → U, identically on C(W). This is natural since
restriction sends each summand to the corresponding composite index and restricts its
section. If W is contained in V, both sums have exactly one summand, and the map is the
identity on C(W). For a point in V, neighborhoods contained in V are cofinal, so this
presheaf map induces a stalk isomorphism. Sheafification preserves stalks and their maps;
conjugating the sheafified map by the two open-extension comparisons gives f with the
claimed stalk isomorphisms. For V empty the condition is vacuous; for V=U the index map
is identity. This is the direct-sum construction of the nested-open arrow in 0A38.
(blueprint: lem-sc-abelian-integer-open-inclusion). -/
theorem abelianIntegerOpen_exists_inclusion
    (X : TopCat.{u}) (U V : Opens X) (hVU : V ≤ U) :
    ∃ f : (abelianOpenExtensionByZero V).obj
          ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj V))
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶
      (abelianOpenExtensionByZero U).obj
          ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))),
      ∀ x : X, x ∈ V →
        IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.hom) := by
  sorry

end TopCat.Sheaf
