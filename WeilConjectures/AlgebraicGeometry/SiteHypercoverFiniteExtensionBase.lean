/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.Basic.Finite.Sigma

/-! # Definitions for finite split simplicial attachment

The helpers spell out the index-level splitting and the matching universal property.

## References

* [Stacks Project, Tag 0DAV](https://stacks.math.columbia.edu/tag/0DAV)
* [Stacks Project, Tag 0DAU](https://stacks.math.columbia.edu/tag/0DAU)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.FormalSplitAttachment

variable {D : Type u} [Category.{v} D] {n : ℕ}

/-- A retained degree. -/
def degree (q : Fin (n + 1)) : SimplexCategory.Truncated n :=
  ⟨SimplexCategory.mk q.val, Nat.le_of_lt_succ q.isLt⟩

/-- The family in a retained degree. -/
def term (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (q : Fin (n + 1)) : FormalCoproduct.{w} D := K.obj (op (degree q))

/-- An ordinal operator on retained degrees. -/
def operator (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    {q r : Fin (n + 1)} (α : SimplexCategory.mk q.val ⟶ SimplexCategory.mk r.val) :
    term K r ⟶ term K q :=
  K.map (SimplexCategory.Truncated.Hom.tr α
    (Nat.le_of_lt_succ q.isLt) (Nat.le_of_lt_succ r.isLt)).op

/-- Indices outside all proper degeneracy images. -/
def IsNondegenerate (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (q : Fin (n + 1)) (i : (term K q).I) : Prop :=
  ¬ ∃ (r : Fin (n + 1)) (_ : r.val < q.val)
    (σ : SimplexCategory.mk q.val ⟶ SimplexCategory.mk r.val),
    Epi σ ∧ ∃ j : (term K r).I, (operator K σ).f j = i

/-- Normalized split labels, including the identity label. -/
def Labels (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) (q : ℕ) :=
  Σ r : Fin (n + 1),
    {σ : SimplexCategory.mk q ⟶ SimplexCategory.mk r.val // Epi σ} ×
      {i : (term K r).I // IsNondegenerate K r i}

/-- The canonical label-to-index map. -/
def labelIndex (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (q : Fin (n + 1)) (a : Labels K q.val) : (term K q).I :=
  (operator K a.2.1.val).f a.2.2.val

/-- The split condition: bijective index normalization and
isomorphisms on every normalized component. -/
def IsSplit (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) : Prop :=
  (∀ q : Fin (n + 1), Function.Bijective (labelIndex K q)) ∧
    ∀ (q : Fin (n + 1)) (a : Labels K q.val),
      IsIso ((operator K a.2.1.val).φ a.2.2.val)

/-- Compatible boundary projections, indexed by all lower simplices. Restriction to
codimension-one faces and their pairwise overlaps gives the finite boundary diagram;
conversely, every lower simplex factors through a face, uniquely up to those overlaps.
In dimension one this is just two projections with no compatibility equations. -/
structure BoundaryCone (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (T : FormalCoproduct.{w} D) where
  projection : ∀ (q : Fin (n + 1)),
    (SimplexCategory.mk q.val ⟶ SimplexCategory.mk (n + 1)) → (T ⟶ term K q)
  naturality : ∀ (q r : Fin (n + 1))
    (α : SimplexCategory.mk q.val ⟶ SimplexCategory.mk r.val)
    (β : SimplexCategory.mk r.val ⟶ SimplexCategory.mk (n + 1)),
    projection r β ≫ operator K α = projection q (α ≫ β)

/-- The universal property of the boundary matching object. -/
def IsMatching (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    {M : FormalCoproduct.{w} D} (c : BoundaryCone K M) : Prop :=
  ∀ (T : FormalCoproduct.{w} D) (p : BoundaryCone K T),
    ∃! f : T ⟶ M, ∀ (q : Fin (n + 1))
      (α : SimplexCategory.mk q.val ⟶ SimplexCategory.mk (n + 1)),
      f ≫ c.projection q α = p.projection q α

/-- The new family, indexed by new simplices and old proper degeneracies. -/
def attachedFamily (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (V : FormalCoproduct.{w} D) : FormalCoproduct.{w} D :=
  ⟨V.I ⊕ Labels K (n + 1),
    Sum.elim V.obj (fun a ↦ (term K a.1).obj a.2.2.val)⟩

/-- Inclusion of the new family. -/
def newInclusion (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (V : FormalCoproduct.{w} D) : V ⟶ attachedFamily K V :=
  ⟨Sum.inl, fun _ ↦ 𝟙 _⟩

/-- Inclusion of an old normalized summand. -/
def oldInclusion (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (V : FormalCoproduct.{w} D) (a : Labels K (n + 1)) :
    (FormalCoproduct.incl D).obj ((term K a.1).obj a.2.2.val) ⟶ attachedFamily K V :=
  FormalCoproduct.Hom.fromIncl (Sum.inr a) (𝟙 _)

/-- The unique normalized label of an old simplex. -/
noncomputable def normalization
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) (hs : IsSplit K)
    (q : Fin (n + 1)) : (term K q).I ≃ Labels K q.val :=
  (Equiv.ofBijective (labelIndex K q) (hs.1 q)).symm

/-- Precompose a normalized degeneracy label with an epimorphism. -/
def precomposeLabel (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    {q r : ℕ} (a : Labels K r) (σ : SimplexCategory.mk q ⟶ SimplexCategory.mk r)
    (hσ : Epi σ) : Labels K q :=
  ⟨a.1, ⟨⟨σ ≫ a.2.1.val, by have := a.2.1.property; exact epi_comp _ _⟩, a.2.2⟩⟩

/-- Normalized labels form a finite set whenever all retained index sets are finite. -/
theorem finite_labels (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (hf : ∀ q : Fin (n + 1), Finite (term K q).I) (q : ℕ) : Finite (Labels K q) := by
  have (r : Fin (n + 1)) : Finite (term K r).I := hf r
  dsimp [Labels]
  infer_instance

end CategoryTheory.FormalSplitAttachment
