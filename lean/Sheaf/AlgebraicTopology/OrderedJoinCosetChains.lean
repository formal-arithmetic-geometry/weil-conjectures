/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J5
-/
module

public import Sheaf.AlgebraicTopology.OrderedJoinChains
public import Mathlib.Algebra.Group.Subgroup.Basic

/-! # Tuple chains and the explicit ordered-coset comparison

The constructions are extracted verbatim from `OrderedJoinCosetComparison` so
that the recursive comparison and erasure lemmas can depend on the data without
importing the theorem that combines them.

Source: direct-images paragraph (3), agent arithmetic expansion, calculations 1–7
(blueprint: def-sfb-ordered-join-coset-chains).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped BigOperators

namespace AlgebraicTopology.OrderedJoin.CosetComparison

/-- Ordered tuples, with repetitions, including the empty tuple in degree -1.
Source: direct-images (3), arithmetic calculation 1
(blueprint: lem-sfb-ordered-join-coset-comparison). -/
def TupleSymbol (Y : Type u) (q : ℤ) : Type u :=
  {l : List Y // (l.length : ℤ) = q + 1}

/-- Free integer tuple chains, with specified basis Finsupp.basisSingleOne.
Source: direct-images (3), calculation 1
(blueprint: lem-sfb-ordered-join-coset-comparison). -/
abbrev TupleChain (Y : Type u) (q : ℤ) : Type u := TupleSymbol Y q →₀ ℤ

/-- The tuple basis term, zero if its length does not fit the requested degree.
Source: direct-images (3), calculation 1
(blueprint: lem-sfb-ordered-join-coset-comparison). -/
noncomputable def tupleTerm {Y : Type u} (q : ℤ) (l : List Y) : TupleChain Y q := by
  classical
  exact if h : (l.length : ℤ) = q + 1 then Finsupp.single ⟨l, h⟩ 1 else 0

/-- Alternating deletion; a vertex goes to the empty tuple and its boundary is zero.
Source: direct-images (3), calculation 2
(blueprint: lem-sfb-ordered-join-coset-comparison). -/
noncomputable def tupleBoundary (Y : Type u) (q p : ℤ) :
    TupleChain Y q →ₗ[ℤ] TupleChain Y p :=
  Finsupp.linearCombination ℤ (fun σ ↦
    ((List.range σ.val.length).map (fun t ↦
      (-1 : ℤ) ^ t • tupleTerm p (σ.val.eraseIdx t))).sum)

/-- Apply a map to every tuple coordinate, including the empty tuple.
Source: direct-images (3), calculations 2 and 4
(blueprint: lem-sfb-ordered-join-coset-comparison). -/
noncomputable def tupleMap {Y : Type u} {Z : Type v} (f : Y → Z) (q : ℤ) :
    TupleChain Y q →ₗ[ℤ] TupleChain Z q :=
  Finsupp.linearCombination ℤ (fun σ ↦ tupleTerm q (σ.val.map f))

variable {G : Type u} [Group G]

/-- The separately labeled sets Ha_i, with no distinctness condition on the cosets.
Source: direct-images (3), calculation 1
(blueprint: lem-sfb-ordered-join-coset-comparison). -/
def Coset {n : ℕ} (H : Subgroup G) (a : Fin (n + 1) → G) (i : Fin (n + 1)) :=
  {x : G // ∃ h : H, x = (h : G) * a i}

/-- The chosen vertex ha_i in its labeled coset.
Source: direct-images (3), calculation 1
(blueprint: lem-sfb-ordered-join-coset-comparison). -/
def vertex {n : ℕ} (H : Subgroup G) (a : Fin (n + 1) → G) (h : H)
    (i : Fin (n + 1)) : Coset H a i := ⟨(h : G) * a i, h, rfl⟩

/-- Left translation preserves each labeled coset.
Source: direct-images (3), calculation 4
(blueprint: lem-sfb-ordered-join-coset-comparison). -/
def translateVertex {n : ℕ} (H : Subgroup G) (a : Fin (n + 1) → G)
    (g : H) (i : Fin (n + 1)) (x : Coset H a i) : Coset H a i :=
  ⟨(g : G) * x.val, by
    obtain ⟨h, hh⟩ := x.property
    exact ⟨g * h, by simp only [hh, Subgroup.coe_mul, mul_assoc]⟩⟩

/-- Degree of an arity-k tuple: -1 for the empty tuple and q for arity q+1.
Source: direct-images (3), augmented indexing convention
(blueprint: lem-sfb-ordered-join-coset-comparison). -/
def arityDegree : ℕ → ℤ
  | 0 => -1
  | q + 1 => (q : ℤ)

/-- The explicit comparison: arity zero is the identity on the empty symbol;
arity one sends h to (0,ha_0); higher arities use S based at the first coordinate,
after the preceding comparison applied to the alternating boundary. The fallback
head 1 is never used on the nonempty symbols in these branches.
Source: direct-images (3), calculations 1 and 3
(blueprint: lem-sfb-ordered-join-coset-comparison). -/
noncomputable def comparison {n : ℕ} (H : Subgroup G) (a : Fin (n + 1) → G) :
    (k : ℕ) → TupleChain H (arityDegree k) →ₗ[ℤ] Chain (Coset H a) (arityDegree k)
  | 0 => Finsupp.linearCombination ℤ (fun _ ↦
      symbolTerm (Coset H a) (-1) ⟨∅, fun i hi ↦ False.elim (Finset.notMem_empty i hi)⟩)
  | 1 => Finsupp.linearCombination ℤ (fun σ ↦
      symbolTerm (Coset H a) 0
        (insert (vertex H a (σ.val.headD 1)) 0
          ⟨∅, fun i hi ↦ False.elim (Finset.notMem_empty i hi)⟩))
  | k + 2 => Finsupp.linearCombination ℤ (fun σ ↦
      contraction (vertex H a (σ.val.headD 1)) (k : ℤ)
        ((k + 1 : ℕ) : ℤ)
        (comparison H a (k + 1)
          (tupleBoundary H ((k + 1 : ℕ) : ℤ) (k : ℤ)
            (Finsupp.single σ 1))))

/-- Erase colors in increasing order, then extend on the specified bases.
Source: direct-images (3), calculation 6
(blueprint: lem-sfb-ordered-join-coset-comparison). -/
noncomputable def erasure {n : ℕ} (H : Subgroup G) (a : Fin (n + 1) → G) (q : ℤ) :
    Chain (Coset H a) q →ₗ[ℤ] TupleChain G q :=
  Finsupp.linearCombination ℤ (fun σ ↦ tupleTerm q
    ((List.finRange (n + 1)).filterMap (fun i ↦
      if hi : i ∈ σ.val.colors then some (σ.val.vertex i hi).val else none)))

/-- A=eP, indexed by arity, including the augmented degree.
Source: direct-images (3), calculation 7
(blueprint: lem-sfb-ordered-join-coset-comparison). -/
noncomputable def erasedComparison {n : ℕ} (H : Subgroup G) (a : Fin (n + 1) → G)
    (k : ℕ) : TupleChain H (arityDegree k) →ₗ[ℤ] TupleChain G (arityDegree k) :=
  (erasure H a (arityDegree k)).comp (comparison H a k)

end AlgebraicTopology.OrderedJoin.CosetComparison
