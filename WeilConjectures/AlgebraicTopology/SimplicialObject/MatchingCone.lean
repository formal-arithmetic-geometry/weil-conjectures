/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicTopology.SimplicialObject.AttachCells
public import WeilConjectures.CategoryTheory.SimplicialBoundaryFaces
public import WeilConjectures.CategoryTheory.SimplicialMatchingObject
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Multiequalizer
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

/-!
# Matching objects of simplicial objects

For a simplicial object `W` in a category `C`, a boundary cone `c : BoundaryCone W n M`
(a compatible family of maps from `M` to the simplices of `W` on the boundary of the
`n`-simplex) is a *matching cone* if every boundary cone factors uniquely through it.

## Main definitions and results

- `CategoryTheory.SimplicialObject.IsMatchingCone`: the universal property.
- `CategoryTheory.SimplicialObject.matchingObj`: a matching object, when `C` has finite limits,
  built as the terminal object (`n = 0`), the product of two copies of `W _⦋0⦌` (`n = 1`)
  and a multiequalizer of faces (`n ≥ 2`).
- `CategoryTheory.SimplicialObject.isMatchingCone_map_matchingObjCone`: functors preserving
  finite limits preserve this matching object.
- `CategoryTheory.SimplicialObject.IsMatchingCone.postcomp`: matching cones can be transported
  along maps of simplicial objects which are isomorphisms in degrees `< n`.
-/

@[expose] public section

noncomputable section

universe v u v' u'

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

namespace BoundaryCone

variable {W : SimplicialObject C} {n : ℕ} {N : C}

/-- The image of a boundary cone under a functor. -/
@[simps]
def map (c : BoundaryCone W n N) {D : Type u'} [Category.{v'} D] (G : C ⥤ D) :
    BoundaryCone (W ⋙ G) n (G.obj N) where
  π Δ h θ := G.map (c.π Δ h θ)
  w Δ Δ' h h' α θ := by
    simp only [Functor.comp_map, ← G.map_comp]
    rw [c.w]

/-- Boundary cones in degree `0` are unique (there is nothing to specify). -/
lemma eq_of_zero (c d : BoundaryCone W 0 N) : c = d :=
  ext' fun _ hΔ _ ↦ absurd hΔ (Nat.not_lt_zero _)

/-- The faces of a boundary cone of degree `n + 1` form a boundary family. -/
lemma isBoundaryFamily_faces {n : ℕ} (c : BoundaryCone W (n + 1) N) :
    W.IsBoundaryFamily (fun j : Fin (n + 2) ↦ c.π ⦋n⦌ (by simp) (SimplexCategory.δ j)) := by
  sorry

/-- Two boundary cones of degree `n + 1` with the same faces are equal. -/
lemma ext_of_faces {n : ℕ} {c d : BoundaryCone W (n + 1) N}
    (h : ∀ j : Fin (n + 2), c.π ⦋n⦌ (by simp) (SimplexCategory.δ j) =
      d.π ⦋n⦌ (by simp) (SimplexCategory.δ j)) : c = d := by
  sorry

/-- The boundary cone of degree `n + 1` determined by a boundary family of faces. -/
def ofFaces {n : ℕ} (x : Fin (n + 2) → (N ⟶ W _⦋n⦌)) (hx : W.IsBoundaryFamily x) :
    BoundaryCone W (n + 1) N :=
  sorry

@[simp]
lemma ofFaces_π_δ {n : ℕ} (x : Fin (n + 2) → (N ⟶ W _⦋n⦌)) (hx : W.IsBoundaryFamily x)
    (j : Fin (n + 2)) : (ofFaces x hx).π ⦋n⦌ (by simp) (SimplexCategory.δ j) = x j := by
  sorry

end BoundaryCone

/-- A boundary cone `c` on `M` is a *matching cone* if every boundary cone factors uniquely
through it. -/
def IsMatchingCone (W : SimplicialObject C) (n : ℕ) {M : C} (c : BoundaryCone W n M) :
    Prop :=
  ∀ (T : C) (p : BoundaryCone W n T), ∃! f : T ⟶ M, c.precomp f = p

namespace IsMatchingCone

variable {W : SimplicialObject C} {n : ℕ} {M : C} {c : BoundaryCone W n M}

/-- The factorisation of a boundary cone through a matching cone. -/
def lift (hc : IsMatchingCone W n c) {T : C} (p : BoundaryCone W n T) : T ⟶ M :=
  (hc T p).exists.choose

@[simp]
lemma precomp_lift (hc : IsMatchingCone W n c) {T : C} (p : BoundaryCone W n T) :
    c.precomp (hc.lift p) = p :=
  (hc T p).exists.choose_spec

lemma hom_ext (hc : IsMatchingCone W n c) {T : C} {f g : T ⟶ M}
    (h : c.precomp f = c.precomp g) : f = g :=
  (hc T (c.precomp g)).unique h rfl

lemma eq_lift (hc : IsMatchingCone W n c) {T : C} {p : BoundaryCone W n T} {f : T ⟶ M}
    (h : c.precomp f = p) : f = hc.lift p :=
  hc.hom_ext (by rw [h, precomp_lift])

/-- Matching cones can be transported along maps of simplicial objects which are isomorphisms
in degrees `< n`. -/
theorem postcomp {W' : SimplicialObject C} (f : W ⟶ W')
    (hf : ∀ k : SimplexCategory, k.len < n → IsIso (f.app (op k)))
    (hc : IsMatchingCone W n c) : IsMatchingCone W' n (c.postcomp f) := by
  sorry

end IsMatchingCone

section MatchingObj

variable [HasFiniteLimits C]

instance (W : SimplicialObject C) (n : ℕ) :
    HasMultiequalizer (matchingBoundaryIndex W n) := by
  have : Fintype (matchingBoundaryShape n).L :=
    inferInstanceAs (Fintype (Fin (n + 3)))
  have : Fintype (matchingBoundaryShape n).R :=
    inferInstanceAs (Fintype {p : Fin (n + 3) × Fin (n + 3) // p.1 < p.2})
  have : DecidableEq (matchingBoundaryShape n).L :=
    inferInstanceAs (DecidableEq (Fin (n + 3)))
  have : DecidableEq (matchingBoundaryShape n).R :=
    inferInstanceAs (DecidableEq {p : Fin (n + 3) × Fin (n + 3) // p.1 < p.2})
  infer_instance

/-- The `n`-th matching object of a simplicial object in a category with finite limits. -/
def matchingObj (W : SimplicialObject C) : ℕ → C
  | 0 => ⊤_ C
  | 1 => ∏ᶜ fun _ : Fin 2 ↦ W _⦋0⦌
  | n + 2 => multiequalizer (matchingBoundaryIndex W n)

/-- The universal boundary cone on the `n`-th matching object. -/
def matchingObjCone (W : SimplicialObject C) : ∀ n : ℕ, BoundaryCone W n (matchingObj W n)
  | 0 => ⟨fun _ h _ ↦ absurd h (Nat.not_lt_zero _), fun _ _ h ↦ absurd h (Nat.not_lt_zero _)⟩
  | 1 => sorry
  | n + 2 => sorry

theorem isMatchingCone_matchingObjCone (W : SimplicialObject C) (n : ℕ) :
    IsMatchingCone W n (matchingObjCone W n) := by
  sorry

/-- Functors preserving finite limits preserve the matching objects. -/
theorem isMatchingCone_map_matchingObjCone {D : Type u'} [Category.{v'} D]
    (G : C ⥤ D) [PreservesFiniteLimits G] (W : SimplicialObject C) (n : ℕ) :
    IsMatchingCone (W ⋙ G) n ((matchingObjCone W n).map G) := by
  sorry

end MatchingObj

end CategoryTheory.SimplicialObject
