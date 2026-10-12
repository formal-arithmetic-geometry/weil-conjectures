/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Sheaf.CategoryTheory.RoosFinitePrefixes
public import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Acyclicity of finite-prefix towers

Source: Stacks Project, Tag 07KW, Lemma 15.88.1 (3).
(blueprint: lem-pc-roos-prefix-acyclic).
-/

@[expose] public section

universe u

namespace CategoryTheory

open Limits

/-- A finite-prefix tower is acyclic for inverse limits.

Source: Stacks Project, Tag 07KW, Lemma 15.88.1 (3).
(blueprint: lem-pc-roos-prefix-acyclic).

Proof: `roosPrefix_transition_surjective` proves that the transition from prefix
n+1+s to n+s is restriction and is surjective by extension by zero. Embed the tower
into a split tower I of injective
abelian groups, using coordinatewise embeddings and products of earlier levels.
The cokernel tower Q again has surjective transitions. The tower I is injective:
lifts of a map across a monomorphism are constructed successively, correcting
along the injective kernel of each split transition. Inverse limits send the
short exact sequence 0 → B → I → Q → 0 to a surjection lim I → lim Q, since
compatible lifts may be corrected in the surjective kernel tower B. Its derived
long exact sequence gives R¹ lim B = 0. The same sequence identifies R^(q+1) lim B
with R^q lim Q for q ≥ 1. Induction over all surjective towers gives vanishing in
every positive degree. Apply this to B = roosPrefixFunctor s A; for s = 0 the
initial empty prefix is the zero group, and extension by zero still applies. -/
theorem roosPrefixAcyclic
    [EnoughInjectives (ℕᵒᵖ ⥤ AddCommGrpCat.{u})]
    [(lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).Additive]
    (s : ℕ) (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :
    ∀ q : ℕ, 1 ≤ q → IsZero ((lim.rightDerived q).obj ((roosPrefixFunctor s).obj A)) := by
  sorry

end CategoryTheory
