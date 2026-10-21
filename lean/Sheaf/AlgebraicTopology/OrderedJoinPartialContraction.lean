/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.List.FinRange
public import Mathlib.LinearAlgebra.FreeModule.Basic

/-! # Partial contraction of ordered join chains

Source: main-20261015 blueprint, six-functors direct-images proof, paragraph (3),
agent arithmetic expansion below local continuous-cocycle descent. The explicit
ordered-join calculation is agent-written, not asserted in the blueprint itself
(blueprint: lem-sfb-ordered-join-partial-contraction).

A face is a finite set of colors with one vertex of each color. Its order is the
increasing order of colors, so no ordering or decidable equality of vertices is
needed. Degree-q chains are finitely supported integer functions on faces with
q+1 vertices; their specified basis is Mathlib's `Finsupp.basisSingleOne`.
The empty face gives degree -1 and there are no faces in other excluded degrees.

The two degree arguments of `boundary`, `insertion`, and `contraction` specify
source and target. In the theorem they are always adjacent, as prescribed. This
avoids type transports between equal integer expressions such as (q+1)-1 and q.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped BigOperators

namespace AlgebraicTopology.OrderedJoin

/-- A face, including the empty face, with its vertices indexed by its colors.
Source: direct-images paragraph (3), agent ordered-join expansion
(blueprint: lem-sfb-ordered-join-partial-contraction). -/
structure Face {r : ℕ} (X : Fin r → Type u) where
  colors : Finset (Fin r)
  vertex : ∀ i : Fin r, i ∈ colors → X i

/-- Degree-q ordered symbols: the integer cardinality condition also includes
q=-1 and excludes q<-1 and q>=r. Source: direct-images paragraph (3), agent
ordered-join expansion (blueprint: lem-sfb-ordered-join-partial-contraction). -/
def Symbol {r : ℕ} (X : Fin r → Type u) (q : ℤ) : Type u :=
  {σ : Face X // (σ.colors.card : ℤ) = q + 1}

/-- The specified free integer module on the degree-q symbols, with specified
basis `Finsupp.basisSingleOne`; this is the basis notion of
`def-weil-pbc-free-module`. Source: direct-images paragraph (3), agent
ordered-join expansion (blueprint: lem-sfb-ordered-join-partial-contraction). -/
abbrev Chain {r : ℕ} (X : Fin r → Type u) (q : ℤ) : Type u :=
  Symbol X q →₀ ℤ

/-- Interpret a face as its basis vector in degree q, or zero if it has the wrong
cardinality. The test concerns only colors. Source: direct-images paragraph (3),
agent ordered-join expansion (blueprint: lem-sfb-ordered-join-partial-contraction). -/
noncomputable def symbolTerm {r : ℕ} (X : Fin r → Type u) (q : ℤ)
    (σ : Face X) : Chain X q := by
  classical
  exact if h : (σ.colors.card : ℤ) = q + 1 then Finsupp.single ⟨σ, h⟩ 1 else 0

/-- Delete the vertex of color i. Source: direct-images paragraph (3), agent
ordered-join expansion (blueprint: lem-sfb-ordered-join-partial-contraction). -/
def erase {r : ℕ} {X : Fin r → Type u} (σ : Face X) (i : Fin r) : Face X where
  colors := σ.colors.erase i
  vertex j hj := σ.vertex j (Finset.mem_of_mem_erase hj)

/-- Replace precisely the vertices with colors in A by their chosen vertices.
The test uses only color membership. Source: direct-images paragraph (3), agent
ordered-join expansion (blueprint: lem-sfb-ordered-join-partial-contraction). -/
def replaceColors {r : ℕ} {X : Fin r → Type u} (v : ∀ i : Fin r, X i)
    (A : Finset (Fin r)) (σ : Face X) : Face X where
  colors := σ.colors
  vertex j hj := if j ∈ A then v j else σ.vertex j hj

/-- Insert the chosen vertex of color i, using increasing color order. The
existing vertex is replaced if i was already present; `insertion` uses this
only when i is missing. Source: direct-images paragraph (3), agent ordered-join
expansion (blueprint: lem-sfb-ordered-join-partial-contraction). -/
def insert {r : ℕ} {X : Fin r → Type u} (v : ∀ i : Fin r, X i)
    (i : Fin r) (σ : Face X) : Face X where
  colors := Insert.insert i σ.colors
  vertex j hj := if h : j = i then h.symm ▸ v i
    else σ.vertex j ((Finset.mem_insert.mp hj).resolve_left h)

/-- The sign of the position of color i: the number of earlier colors.
Source: direct-images paragraph (3), agent ordered-join expansion
(blueprint: lem-sfb-ordered-join-partial-contraction). -/
def positionSign {r : ℕ} (C : Finset (Fin r)) (i : Fin r) : ℤ :=
  (-1 : ℤ) ^ (C.filter (fun j ↦ j < i)).card

/-- Alternating deletion, extended from the specified basis. The component
from q to q-1 is d; in particular a singleton maps to the empty face and the
empty face maps to zero. Source: direct-images paragraph (3), agent ordered-join
expansion (blueprint: lem-sfb-ordered-join-partial-contraction). -/
noncomputable def boundary {r : ℕ} (X : Fin r → Type u) (q p : ℤ) :
    Chain X q →ₗ[ℤ] Chain X p :=
  Finsupp.linearCombination ℤ (fun σ : Symbol X q ↦
    ∑ i ∈ σ.val.colors, positionSign σ.val.colors i • symbolTerm X p (erase σ.val i))

/-- The signed insertion c_i, zero on faces already containing i, extended
linearly from the basis. Its degree-one component has p=q+1.
Source: direct-images paragraph (3), agent ordered-join expansion
(blueprint: lem-sfb-ordered-join-partial-contraction). -/
noncomputable def insertion {r : ℕ} {X : Fin r → Type u} (v : ∀ i : Fin r, X i)
    (i : Fin r) (q p : ℤ) : Chain X q →ₗ[ℤ] Chain X p :=
  Finsupp.linearCombination ℤ (fun σ : Symbol X q ↦
    if i ∈ σ.val.colors then 0
    else positionSign σ.val.colors i • symbolTerm X p (insert v i σ.val))

/-- R_i is zero on missing-color symbols, and otherwise the original symbol
minus the symbol with its color-i vertex replaced by v_i.
Source: direct-images paragraph (3), agent ordered-join expansion
(blueprint: lem-sfb-ordered-join-partial-contraction). -/
noncomputable def remainder {r : ℕ} {X : Fin r → Type u} (v : ∀ i : Fin r, X i)
    (i : Fin r) (q : ℤ) : Chain X q →ₗ[ℤ] Chain X q :=
  Finsupp.linearCombination ℤ (fun σ : Symbol X q ↦
    if i ∈ σ.val.colors then
      symbolTerm X q σ.val - symbolTerm X q (replaceColors v {i} σ.val)
    else 0)

/-- The ordered prefix R_0 composed with ... composed with R_{n-1}; the rightmost
factor acts first. The empty prefix is the identity. Only n<=r is used.
Source: direct-images paragraph (3), agent ordered-join expansion
(blueprint: lem-sfb-ordered-join-partial-contraction). -/
noncomputable def remainderPrefix {r : ℕ} {X : Fin r → Type u} (v : ∀ i : Fin r, X i)
    (n : ℕ) (q : ℤ) : Chain X q →ₗ[ℤ] Chain X q :=
  (List.range n).foldr (fun j P ↦
    if h : j < r then (remainder v ⟨j, h⟩ q).comp P else P) LinearMap.id

/-- The displayed S=sum_i (R_0 composed with ... composed with R_{i-1}) c_i.
Its degree-one component is `contraction v q (q+1)`.
Source: direct-images paragraph (3), agent ordered-join expansion
(blueprint: lem-sfb-ordered-join-partial-contraction). -/
noncomputable def contraction {r : ℕ} {X : Fin r → Type u}
    (v : ∀ i : Fin r, X i) (q p : ℤ) : Chain X q →ₗ[ℤ] Chain X p :=
  ∑ i : Fin r, (remainderPrefix v i.val p).comp (insertion v i q p)

/-- Apply the given maps to vertices, preserving colors.
Source: direct-images paragraph (3), agent ordered-join expansion
(blueprint: lem-sfb-ordered-join-partial-contraction). -/
def mapFace {r : ℕ} {X : Fin r → Type u} {Y : Fin r → Type v}
    (f : ∀ i : Fin r, X i → Y i) (σ : Face X) : Face Y where
  colors := σ.colors
  vertex i hi := f i (σ.vertex i hi)

/-- The induced integer-linear map J_q(f), with no injectivity assumption.
Source: direct-images paragraph (3), agent ordered-join expansion
(blueprint: lem-sfb-ordered-join-partial-contraction). -/
noncomputable def chainMap {r : ℕ} {X : Fin r → Type u} {Y : Fin r → Type v}
    (f : ∀ i : Fin r, X i → Y i) (q : ℤ) : Chain X q →ₗ[ℤ] Chain Y q :=
  Finsupp.linearCombination ℤ (fun σ : Symbol X q ↦ symbolTerm Y q (mapFace f σ.val))

/-- The unreduced list of coefficients, insertion colors and replacement sets.
For each absent color i whose predecessors are present, list all subsets A of
its predecessors with sign (-1)^(position(i)+card A). This list depends only on
r and the color set C, and never examines vertices or combines equal symbols.
Source: direct-images paragraph (3), agent ordered-join expansion
(blueprint: lem-sfb-ordered-join-partial-contraction). -/
noncomputable def expansionRecipe (r : ℕ) (C : Finset (Fin r)) :
    List (ℤ × (Fin r × Finset (Fin r))) :=
  (List.finRange r).flatMap (fun i ↦
    if i ∈ C then []
    else if (Finset.univ.filter (fun j : Fin r ↦ j < i)) ⊆ C then
      ((Finset.univ.filter (fun j : Fin r ↦ j < i)).powerset.toList.map
        (fun A ↦ (positionSign C i * (-1 : ℤ) ^ A.card, (i, A))))
    else [])

/-- The boundary squares to zero, S contracts all degrees below the top,
is natural for arbitrary maps of pointed families, and has the finite
color-dependent expansion specified by `expansionRecipe`.

Source: direct-images paragraph (3), agent ordered-join expansion, calculations
1-8; this is not asserted in the blueprint itself
(blueprint: lem-sfb-ordered-join-partial-contraction).

Proof:
1. Extend each basis formula by finite integer linear combination, using
   def-weil-pbc-free-module. Equality of maps is checked on these bases.
2. In d squared, deleting original positions a<b in the two possible orders
   gives signs (-1)^(a+b-1) and (-1)^(a+b), which cancel. In degrees 0 and -1
   the second boundary is zero. The same holds on all zero chain groups.
3. For a symbol missing color i, let k count its colors less than i. Deleting
   the inserted vertex from dc_i has sign (-1)^(2k)=1. Deletions of original
   vertices cancel with c_i d: for a<k the signs are (-1)^(k+a) and
   (-1)^(a+k-1), and for a>=k they are (-1)^(k+a+1) and (-1)^(a+k).
   Thus dc_i+c_i d=1-R_i, including the empty symbol.
4. For a symbol containing color i in position k, c_i is zero; only the k-th
   face can contribute to c_i d, giving the chosen replacement with sign
   (-1)^(2k)=1. Again dc_i+c_i d=1-R_i, including the top degree.
5. Using d squared zero, deduce dR_i=R_i d. The ordered prefixes P_i commute
   with d, so dS+Sd=sum_i P_i(1-R_i)=sum_i(P_i-P_{i+1})=1-P_r.
6. In degrees -1 through r-2 every symbol misses some color j. Replacement
   preserves the color set, so the factor R_j kills all terms reaching it in
   P_r. Therefore P_r=0. On the empty face only i=0 survives, giving
   S_{-1}[empty]=[(0,v_0)] and dS_{-1}=1; the degree -2 group is zero.
7. Applying f preserves colors, insertion positions, chosen insertions, and
   replacements. It commutes with every c_i and R_i, hence with S. Coincident
   output symbols may cancel, so injectivity of the vertex maps is unnecessary.
8. The i-th summand vanishes if i is present or some predecessor is missing.
   Otherwise distribute the factors R_j=1-T_j for j<i. Each subset A records
   the negative replacement choices, with coefficient
   (-1)^position(i) times (-1)^card(A). These are exactly `expansionRecipe`;
   coincident symbols are left uncollected and no equality of vertices is tested. -/
theorem partialContraction (r : ℕ) (hr : 1 ≤ r) (X : Fin r → Type u)
    (v : ∀ i : Fin r, X i) :
    (∀ q : ℤ, (boundary X (q - 1) (q - 2)).comp (boundary X q (q - 1)) = 0) ∧
    (∀ q : ℤ, -1 ≤ q → q ≤ (r : ℤ) - 2 →
      (boundary X (q + 1) q).comp (contraction v q (q + 1)) +
        (contraction v (q - 1) q).comp (boundary X q (q - 1)) = LinearMap.id) ∧
    contraction v (-2) (-1) = 0 ∧
    (∀ (Y : Fin r → Type v) (f : ∀ i : Fin r, X i → Y i) (q : ℤ),
      (chainMap f (q + 1)).comp (contraction v q (q + 1)) =
        (contraction (fun i ↦ f i (v i)) q (q + 1)).comp (chainMap f q)) ∧
    (∀ (q : ℤ) (σ : Symbol X q),
      contraction v q (q + 1) (Finsupp.single σ 1) =
        ((expansionRecipe r σ.val.colors).map (fun t ↦
          t.1 • symbolTerm X (q + 1) (insert v t.2.1 (replaceColors v t.2.2 σ.val)))).sum) := by
  sorry

end AlgebraicTopology.OrderedJoin
