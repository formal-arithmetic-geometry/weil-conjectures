/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteMultiequalizer
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Matching objects of simplicial objects

Source: Stacks Project, Tags 0186, 0167, 002O
(blueprint: lem-weil-pbc-simplicial-matching-object).
The boundary diagrams in degrees zero and one are empty and discrete, respectively.
The multicospan below is the boundary diagram in degree `n + 2`.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

/-- The finite shape of the boundary diagram in degree `n + 2`: faces and pairs of faces.
Source: Stacks, Tag 0186 (blueprint: lem-weil-pbc-simplicial-matching-object). -/
def matchingBoundaryShape (n : ℕ) : MulticospanShape where
  L := Fin (n + 3)
  R := {p : Fin (n + 3) × Fin (n + 3) // p.1 < p.2}
  fst p := p.val.1
  snd p := p.val.2

/-- The diagram `D_(n+2)(K)`, with arrows `d_(j-1)` from face `i` and `d_i` from face `j`.
Source: Stacks, Tag 0186 (blueprint: lem-weil-pbc-simplicial-matching-object). -/
def matchingBoundaryIndex {C : Type u} [Category.{v} C] (K : SimplicialObject C) (n : ℕ) :
    MulticospanIndex (matchingBoundaryShape n) C where
  left _ := K _⦋n + 1⦌
  right _ := K _⦋n⦌
  fst p := K.δ (p.val.2.pred (Fin.ne_zero_of_lt p.property))
  snd p := K.δ (p.val.1.castLT (Nat.lt_of_lt_of_le p.property
    (Nat.le_of_lt_succ p.val.2.isLt)))

/-- Degree zero: the empty boundary has final object `e` as its limit, unique up to unique
isomorphism, and its matching map is the unique map from `K₀`.
Source: Stacks, Tags 002O, 0186 (blueprint: lem-weil-pbc-simplicial-matching-object).
Proof: the empty diagram has a limit by finite completeness
[def-galois-finite-limits-colimits]; its universal property is finality. Finality gives the
unique map from every object, in particular `K₀`, and the unique comparison isomorphism. -/
theorem matching_object_zero {C : Type u} [Category.{v} C] [HasFiniteLimits C]
    (K : SimplicialObject C) (e : C) (he : IsTerminal e) :
    (∃! μ : K _⦋0⦌ ⟶ e, True) ∧
      (∀ (M : C), IsTerminal M → ∃! α : e ≅ M, True) := by
  sorry

/-- Degree one: the discrete two-object boundary has a product as its limit. Its projections
give a bijection with arbitrary pairs, natural under precomposition, and its matching map is
uniquely specified by `d₀` and `d₁`.
Source: Stacks, Tag 0186 (blueprint: lem-weil-pbc-simplicial-matching-object).
Proof: finite completeness [def-galois-finite-limits-colimits] gives a limit of the discrete
pair. The limit universal property identifies maps to it with pairs, with no equations.
Precomposition commutes with projections, giving naturality. Apply the bijection to the two
face maps [def-weil-pbc-simplicial-object]. Limit uniqueness gives the unique projection-
preserving isomorphism to any other limiting fan. -/
theorem matching_object_one {C : Type u} [Category.{v} C] [HasFiniteLimits C]
    (K : SimplicialObject C) :
    ∃ c : Fan (fun _ : Fin 2 => K _⦋0⦌),
      Nonempty (IsLimit c) ∧
      (∀ (c' : Fan (fun _ : Fin 2 => K _⦋0⦌)), Nonempty (IsLimit c') →
        ∃! α : c.pt ≅ c'.pt, ∀ i : Fin 2, α.hom ≫ c'.proj i = c.proj i) ∧
      (∃ E : ∀ W : C, (W ⟶ c.pt) ≃ (Fin 2 → (W ⟶ K _⦋0⦌)),
        (∀ (W : C) (g : W ⟶ c.pt) (i : Fin 2), E W g i = g ≫ c.proj i) ∧
        (∀ (W W' : C) (f : W' ⟶ W) (g : W ⟶ c.pt) (i : Fin 2),
          E W' (f ≫ g) i = f ≫ E W g i)) ∧
      (∃! μ : K _⦋1⦌ ⟶ c.pt, ∀ i : Fin 2, μ ≫ c.proj i = K.δ i) := by
  sorry

/-- Degrees `n + 2`: existence and uniqueness of the boundary limit, its natural tuple
bijection, the face compatibility identities, and the unique matching morphism.
Source: Stacks, Tags 0186, 0167, 002O
(blueprint: lem-weil-pbc-simplicial-matching-object).
Proof: the index has finitely many faces and pairs and no composable nonidentity arrows.
Finite completeness [def-galois-finite-limits-colimits] therefore gives the limit and its
unique projection-preserving comparison isomorphisms. A cone determines compatible face
maps; conversely compatible face maps determine the component at every pair as their common
composite. The limit universal property is thus exactly the stated tuple bijection, and
precomposition commutes with each projection. The face identity
[lem-weil-pbc-simplex-face-face-identity], transported by the contravariant functor
[def-weil-pbc-simplicial-object], makes the face tuple compatible. The bijection applied to
that tuple gives the unique matching map. -/
theorem matching_object_succ_succ {C : Type u} [Category.{v} C] [HasFiniteLimits C]
    (K : SimplicialObject C) (n : ℕ) :
    ∃ c : Cone (matchingBoundaryIndex K n).multicospan,
      Nonempty (IsLimit c) ∧
      (∀ (c' : Cone (matchingBoundaryIndex K n).multicospan), Nonempty (IsLimit c') →
        ∃! α : c.pt ≅ c'.pt, ∀ j, α.hom ≫ c'.π.app j = c.π.app j) ∧
      (∃ E : ∀ W : C, (W ⟶ c.pt) ≃
        {x : Fin (n + 3) → (W ⟶ K _⦋n + 1⦌) //
          ∀ p : (matchingBoundaryShape n).R,
            x p.val.1 ≫ (matchingBoundaryIndex K n).fst p =
              x p.val.2 ≫ (matchingBoundaryIndex K n).snd p},
        (∀ (W : C) (g : W ⟶ c.pt) (i : Fin (n + 3)),
          (E W g).val i = g ≫ c.π.app (WalkingMulticospan.left i)) ∧
        (∀ (W W' : C) (f : W' ⟶ W) (g : W ⟶ c.pt) (i : Fin (n + 3)),
          (E W' (f ≫ g)).val i = f ≫ (E W g).val i)) ∧
      (∀ p : (matchingBoundaryShape n).R,
        K.δ p.val.1 ≫ (matchingBoundaryIndex K n).fst p =
          K.δ p.val.2 ≫ (matchingBoundaryIndex K n).snd p) ∧
      (∃! μ : K _⦋n + 2⦌ ⟶ c.pt, ∀ i : Fin (n + 3),
        μ ≫ c.π.app (WalkingMulticospan.left i) = K.δ i) := by
  sorry

end CategoryTheory.SimplicialObject
