/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-! # Finite attachment to a split truncated simplicial family

Source: literature/stacks-project/hypercovering.tex, Tags 0DAV and 0DAU
(blueprint: lem-weil-pbc-site-hypercover-finite-extension).

The helpers spell out the index-level splitting and the matching universal property.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.FormalSplitAttachment

variable {D : Type u} [Category.{v} D] {n : ℕ}

/-- A retained degree. Source: Stacks 0DAV
(blueprint: lem-weil-pbc-site-hypercover-finite-extension). -/
def degree (q : Fin (n + 1)) : SimplexCategory.Truncated n :=
  ⟨SimplexCategory.mk q.val, Nat.le_of_lt_succ q.isLt⟩

/-- The family in a retained degree. Source: Stacks 0DAV
(blueprint: lem-weil-pbc-site-hypercover-finite-extension). -/
def term (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (q : Fin (n + 1)) : FormalCoproduct.{w} D := K.obj (op (degree q))

/-- An ordinal operator on retained degrees. Source: Stacks 0DAV
(blueprint: lem-weil-pbc-site-hypercover-finite-extension). -/
def operator (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    {q r : Fin (n + 1)} (α : SimplexCategory.mk q.val ⟶ SimplexCategory.mk r.val) :
    term K r ⟶ term K q :=
  K.map (SimplexCategory.Truncated.Hom.tr α
    (Nat.le_of_lt_succ q.isLt) (Nat.le_of_lt_succ r.isLt)).op

/-- Indices outside all proper degeneracy images. Source: Stacks 0DAU
(blueprint: lem-weil-pbc-site-hypercover-finite-extension). -/
def IsNondegenerate (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (q : Fin (n + 1)) (i : (term K q).I) : Prop :=
  ¬ ∃ (r : Fin (n + 1)) (_ : r.val < q.val)
    (σ : SimplexCategory.mk q.val ⟶ SimplexCategory.mk r.val),
    Epi σ ∧ ∃ j : (term K r).I, (operator K σ).f j = i

/-- Normalized split labels, including the identity label. Source: Stacks 0DAU
(blueprint: lem-weil-pbc-site-hypercover-finite-extension). -/
def Labels (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) (q : ℕ) :=
  Σ r : Fin (n + 1),
    {σ : SimplexCategory.mk q ⟶ SimplexCategory.mk r.val // Epi σ} ×
      {i : (term K r).I // IsNondegenerate K r i}

/-- The canonical label-to-index map. Source: Stacks 0DAU
(blueprint: lem-weil-pbc-site-hypercover-finite-extension). -/
def labelIndex (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (q : Fin (n + 1)) (a : Labels K q.val) : (term K q).I :=
  (operator K a.2.1.val).f a.2.2.val

/-- The explicit split condition of the node: bijective index normalization and
isomorphisms on every normalized component. Source: Stacks 0DAU
(blueprint: lem-weil-pbc-site-hypercover-finite-extension). -/
def IsSplit (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) : Prop :=
  (∀ q : Fin (n + 1), Function.Bijective (labelIndex K q)) ∧
    ∀ (q : Fin (n + 1)) (a : Labels K q.val),
      IsIso ((operator K a.2.1.val).φ a.2.2.val)

/-- Compatible boundary projections, indexed by all lower simplices. Restriction to
codimension-one faces and their pairwise overlaps gives the node's finite boundary diagram;
conversely, every lower simplex factors through a face, uniquely up to those overlaps.
In dimension one this is just two projections with no compatibility equations.
Source: Stacks 0DAV (blueprint: lem-weil-pbc-site-hypercover-finite-extension). -/
structure BoundaryCone (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (T : FormalCoproduct.{w} D) where
  projection : ∀ (q : Fin (n + 1)),
    (SimplexCategory.mk q.val ⟶ SimplexCategory.mk (n + 1)) → (T ⟶ term K q)
  naturality : ∀ (q r : Fin (n + 1))
    (α : SimplexCategory.mk q.val ⟶ SimplexCategory.mk r.val)
    (β : SimplexCategory.mk r.val ⟶ SimplexCategory.mk (n + 1)),
    projection r β ≫ operator K α = projection q (α ≫ β)

/-- The universal property of the boundary matching object. Source: Stacks 0DAV
(blueprint: lem-weil-pbc-site-hypercover-finite-extension). -/
def IsMatching (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    {M : FormalCoproduct.{w} D} (c : BoundaryCone K M) : Prop :=
  ∀ (T : FormalCoproduct.{w} D) (p : BoundaryCone K T),
    ∃! f : T ⟶ M, ∀ (q : Fin (n + 1))
      (α : SimplexCategory.mk q.val ⟶ SimplexCategory.mk (n + 1)),
      f ≫ c.projection q α = p.projection q α

/-- The new family, indexed by new simplices and old proper degeneracies.
Source: Stacks 0DAV (blueprint: lem-weil-pbc-site-hypercover-finite-extension). -/
def attachedFamily (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (V : FormalCoproduct.{w} D) : FormalCoproduct.{w} D :=
  ⟨V.I ⊕ Labels K (n + 1),
    Sum.elim V.obj (fun a ↦ (term K a.1).obj a.2.2.val)⟩

/-- Inclusion of the new family. Source: Stacks 0DAV
(blueprint: lem-weil-pbc-site-hypercover-finite-extension). -/
def newInclusion (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (V : FormalCoproduct.{w} D) : V ⟶ attachedFamily K V :=
  ⟨Sum.inl, fun _ ↦ 𝟙 _⟩

/-- Inclusion of an old normalized summand. Source: Stacks 0DAV
(blueprint: lem-weil-pbc-site-hypercover-finite-extension). -/
def oldInclusion (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (V : FormalCoproduct.{w} D) (a : Labels K (n + 1)) :
    (FormalCoproduct.incl D).obj ((term K a.1).obj a.2.2.val) ⟶ attachedFamily K V :=
  FormalCoproduct.Hom.fromIncl (Sum.inr a) (𝟙 _)

/-- Attach a finite family along its prescribed boundary.
Source: Stacks 0DAV, construction of the extension, and 0DAU, split convention
(blueprint: lem-weil-pbc-site-hypercover-finite-extension).

Proof: Put h=n+1. In every old degree normalize indices as triples (r,σ,i)
using the split bijection and component isomorphisms; in degree h adjoin V.
For α:[q]→[h], q≤n, choose a missing value and factor through its face.
The pairwise boundary equations make the resulting V→K_q independent of the
missing value and compatible with all further operators (for n=0 there is no
pairwise condition). For every ordinal operator on the normalized families,
factor σα uniquely as an injection followed, contravariantly, by a surjection.
Apply the boundary operator (or the old K-operator) for its injective part,
then normalize its image using the split bijection and inverse component
isomorphism. The surjective part just concatenates the label. Composition
holds because the two image factorizations differ by normalization of the
same old K-operator; the inverse component isomorphisms cancel. The exceptional
full-image case is the identity in degree h. Transport back through the old
normalizations to obtain L and its restriction identification. The new indices
are exactly V.I and the displayed face formulas follow from the construction.
Every degree is finite: old indices are finite, their nondegenerate subsets
are finite, and there are finitely many maps between finite ordinals. This uses
only the two recorded simplicial/formal-coproduct dependencies.
-/
theorem exists_split_truncated_extension
    [HasFiniteLimits D]
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (hfinite : ∀ q : Fin (n + 1), Finite (term K q).I) (hsplit : IsSplit K)
    {M : FormalCoproduct.{w} D} (c : BoundaryCone K M) (hc : IsMatching K c)
    (V : FormalCoproduct.{w} D) [Finite V.I] (v : V ⟶ M) :
    ∃ (L : SimplicialObject.Truncated (FormalCoproduct.{w} D) (n + 1))
      (e : (SimplicialObject.Truncated.trunc (FormalCoproduct.{w} D)
        (n + 1) n (Nat.le_succ n)).obj L = K)
      (t : attachedFamily K V = term L ⟨n + 1, Nat.lt_succ_self _⟩)
      (b : term L ⟨n + 1, Nat.lt_succ_self _⟩ ⟶ M),
      IsSplit L ∧
      (∀ q : Fin (n + 2), Finite (term L q).I) ∧
      (∀ x : (term L ⟨n + 1, Nat.lt_succ_self _⟩).I,
        IsNondegenerate L ⟨n + 1, Nat.lt_succ_self _⟩ x ↔
          ∃ j : V.I, (eqToHom t).f (Sum.inl j) = x) ∧
      (∀ (q : Fin (n + 1))
        (α : SimplexCategory.mk q.val ⟶ SimplexCategory.mk (n + 1)),
        b ≫ c.projection q α =
          operator L (q := ⟨q.val, Nat.lt_succ_of_lt q.isLt⟩)
            (r := ⟨n + 1, Nat.lt_succ_self _⟩) α ≫ (eqToHom e).app (op (degree q))) ∧
      (newInclusion K V ≫ eqToHom t ≫ b = v) ∧
      (∀ (a : Labels K (n + 1)) (i : Fin (n + 2)),
        oldInclusion K V a ≫ eqToHom t ≫
          operator L (q := ⟨n, Nat.lt_succ_of_le (Nat.le_succ n)⟩)
            (r := ⟨n + 1, Nat.lt_succ_self _⟩) (SimplexCategory.δ i) ≫
            (eqToHom e).app (op (degree ⟨n, Nat.lt_succ_self _⟩)) =
          FormalCoproduct.Hom.fromIncl a.2.2.val (𝟙 _) ≫
            operator K (q := ⟨n, Nat.lt_succ_self _⟩)
              (SimplexCategory.δ i ≫ a.2.1.val)) := by
  sorry

end CategoryTheory.FormalSplitAttachment
