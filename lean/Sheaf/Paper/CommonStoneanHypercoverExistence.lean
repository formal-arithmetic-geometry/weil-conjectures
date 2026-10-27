/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Mathlib.Topology.Category.Profinite.Basic
public import Mathlib.Topology.ExtremallyDisconnected
public import Sheaf.CategoryTheory.ProperFaceMatchingObject
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-! # Existence of a Stonean hypercover over a profinite base

Source: Stacks, Tags 0DAV and 01G2; Bhatt--Scholze, Example 2.4.6.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology
open scoped Simplicial

namespace AlgebraicGeometry.ProEtale

/-- A profinite base admits an augmented Stonean hypercover with surjective augmentations.

Source: Stacks, Tags 0DAV and 01G2; Bhatt--Scholze, Example 2.4.6.
(blueprint: lem-sfb-common-stonean-hypercover-existence).

Proof: Equip profinite spaces with finite jointly surjective covering families. Pullbacks
are closed subspaces of products. Stonean covers give singleton covers by extremally
disconnected objects; adjoining an arrow preserves joint surjectivity. Apply the finite
basis hypercover existence theorem to P. Realize each finite formal family as the finite
disjoint union of its members, with operators given componentwise. First reindex each
finite family by a finite set in the base universe, transporting operators through
the chosen bijections; this keeps every realized space in that universe. These spaces are
profinite and extremally disconnected, since each summand is clopen. Finite-family
realization preserves finite limits: compatible choices of summands form a finite set,
and each choice determines a clopen piece of the ordinary limit, equal to the limit of
the selected spaces. This includes the empty diagram, whose limit over P is P.
Consequently the formal matching covers realize to surjective matching arrows. The
zero matching cover is a surjection onto P. For each n, the operator opposite to the
unique map [n] to [0] gives a degeneracy from degree zero to degree n over P, so every
augmentation is surjective. When P is empty every object over P is empty, and the
construction and all surjectivity assertions remain valid. -/
theorem exists_common_stonean_hypercover (P : Profinite.{u}) :
    ∃ S : SimplicialObject (Over P),
      ∃ (M : ∀ n : ℕ, Cone (S.properFaceDiagram n))
        (μ : ∀ n : ℕ, S _⦋n⦌ ⟶ (M n).pt),
        (M 0).pt = Over.mk (𝟙 P) ∧
        (∀ n : ℕ, Nonempty (IsLimit (M n))) ∧
        (∀ (n : ℕ) (b : SimplicialObject.ProperFaceCategory n),
          μ n ≫ (M n).π.app (op b) = S.map b.obj.hom.op) ∧
        (∀ n : ℕ, Function.Surjective (μ n).left) ∧
        (∀ n : ℕ, ExtremallyDisconnected (S _⦋n⦌).left) ∧
        (∀ n : ℕ, Function.Surjective (S _⦋n⦌).hom) := by sorry

end AlgebraicGeometry.ProEtale
