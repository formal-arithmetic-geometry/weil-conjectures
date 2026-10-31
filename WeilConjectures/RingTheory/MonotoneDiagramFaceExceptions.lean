/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.SupportedHomogeneousDivision
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Finite exceptional translations of monotone exponent diagrams

Source: the agent quantitative refinement of Bierstone--Milman, Invent. Math. 128 (1997),
Lemma 8.2 and Remarks 8.4, pp. 274--275, recorded in the DAG
(blueprint: lem-trf-monotone-diagram-face-exceptions).

Exponent vectors are the finitely supported exponents `Fin n →₀ ℕ` of
`MvPolynomial (Fin n) ℤ`. Coordinate indices are zero-based.
`none` labels the complementary region, and `some i` labels the region of vertex `α i`.
-/

@[expose] public section

set_option autoImplicit false

namespace MonomialDiagram

/-- The translated disjoint vertex regions, with the complement labelled by `none`.
For `some i`, coordinatewise domination by an earlier vertex is excluded.
Source: Bierstone--Milman 1997, §8, pp. 273--274, in the translated-region convention
(blueprint: lem-trf-monotone-diagram-face-exceptions). -/
def region {n s : ℕ} (D : Set (Fin n →₀ ℕ)) (α : Fin s → Fin n →₀ ℕ) :
    Option (Fin s) → Set (Fin n →₀ ℕ)
  | none => Dᶜ
  | some i => quotientSupport α i

/-- The maximum of `1` and all vertex degrees; the empty list has bound `1`.
Source: the DAG's quantitative refinement of Bierstone--Milman 1997, Lemma 8.2
(blueprint: lem-trf-monotone-diagram-face-exceptions). -/
noncomputable def vertexDegreeBound {n s : ℕ} (α : Fin s → Fin n →₀ ℕ) : ℕ :=
  max 1 (Finset.univ.sup fun i : Fin s ↦ (α i).degree)

/-- Exceptions to translation by the first surviving coordinate on a coordinate face.
Here `r : Fin n` encodes the face with coordinates strictly before `r` equal to zero.
Source: the DAG's refinement of Bierstone--Milman 1997, Remarks 8.4
(blueprint: lem-trf-monotone-diagram-face-exceptions). -/
def faceExceptions {n s : ℕ} (D : Set (Fin n →₀ ℕ)) (α : Fin s → Fin n →₀ ℕ)
    (i : Option (Fin s)) (r : Fin n) : Set (Fin n →₀ ℕ) :=
  {β | β ∈ region D α i ∧ (∀ j : Fin n, j < r → β j = 0) ∧
    β + Finsupp.single r 1 ∉ region D α i}

/-- Every face exception lies in the box bounded by the maximum vertex degree and is finite.
Source: agent quantitative refinement of Bierstone--Milman 1997, Lemma 8.2 and Remarks 8.4,
pp. 274--275 (blueprint: lem-trf-monotone-diagram-face-exceptions).

Proof plan (the seven elementary coordinate steps recorded in the DAG):
1. Every vector in `D` dominates a listed vertex: minimize total degree in the finite box
   below it. Minimality in that box gives coordinatewise minimality in `D`. Conversely,
   domination by a vertex implies membership in `D` by additive closure.
2. For a vertex-region exception, an earlier vertex `α h` lies below `α i + β + e_r`
   but not below `α i + β`. Thus its `r` coordinate equals `α i r + β r + 1`, giving
   `β r < vertexDegreeBound α`.
3. If a later coordinate of `β` reaches the bound, move all the `r` coordinate of `α h`
   to that coordinate. Monotonicity gives a vector `γ` in `D` below `α i + β`.
4. A minimal vertex below `γ` precedes `α h`: its degree is smaller, or it equals `γ`
   at equal degree and is lexicographically smaller at coordinate `r`. This contradicts
   membership in the region of `α i`, and bounds every later coordinate of `β`.
5. For a complementary-region exception, choose a vertex below `β + e_r`. It is not
   below `β`, so its `r` coordinate is `β r + 1`, giving the same bound on `β r`.
6. Moving this coordinate to any later coordinate of `β` that reaches the bound produces
   an element of `D` below `β`, contradicting `β ∉ D`.
7. Coordinates before `r` vanish and all remaining coordinates are less than the bound,
   so the containing box is finite. The empty and full diagrams give empty exception
   sets; in dimension one or on the final face there are no later coordinates to bound.
-/
theorem faceExceptions_subset_box_and_finite {n s : ℕ} (hn : 1 ≤ n)
    (D : Set (Fin n →₀ ℕ))
    (hD : IsMonotone D) (α : Fin s → Fin n →₀ ℕ)
    (hα : IsOrderedVertexFamily D α)
    (i : Option (Fin s)) (r : Fin n) :
    faceExceptions D α i r ⊆
      {β | (∀ j : Fin n, j < r → β j = 0) ∧
        ∀ j : Fin n, r ≤ j → β j < vertexDegreeBound α} ∧
    (faceExceptions D α i r).Finite := by
  sorry

end MonomialDiagram
