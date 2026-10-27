# AlgebraicTopology.OrderedJoin.CosetComparison.TupleSymbol

## Reason

The explicit data and the bundled theorem originally occupied one module. Separate
recursive-comparison and erasure lemmas must import these data, while the bundled
theorem imports those lemmas. Move the data verbatim to a new module and publicly
reexport it from the original module to avoid that import cycle. All names,
signatures, bodies, reducibility and attributes stay identical. No source-library
module changes.

## Old

Module `Sheaf.AlgebraicTopology.OrderedJoinCosetComparison` contained:

```lean
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

```

## New

The following exact same text is now in
`Sheaf.AlgebraicTopology.OrderedJoinCosetChains`. The original module adds
`public import Sheaf.AlgebraicTopology.OrderedJoinCosetChains`, retaining its
existing public imports and unchanged theorem statement:

```lean
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

```

## Users

`python3 tools/downstream.py Sheaf.AlgebraicTopology.OrderedJoinCosetComparison
--uses AlgebraicTopology.OrderedJoin.CosetComparison.TupleSymbol` reported zero
existing downstream modules and only the original module itself as a user.
A direct import search and a search for all construction names agree: no other
existing Lean module imports or references the assigned module. Its DAG parents
with unfinished proofs remain intact; nothing is withdrawn or pruned.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicTopology.OrderedJoinCosetComparison | J5 | Same public declarations by reexport; theorem now combines the new lemmas and direct proofs. |
| Sheaf.AlgebraicTopology.OrderedJoinCosetRecursion | J5, new module | Uses the unchanged data to state the remaining recursive comparison argument. |
| Sheaf.AlgebraicTopology.OrderedJoinCosetErasureBoundary | J5, new module | Uses the unchanged data to state erasure-boundary compatibility. |

No target statement or definition changes its meaning. The relocated definitions
are actual constructions with no proof holes, chosen data, or new instances.

## Status

landed 20261026T091820-L-3378067 2026-10-26 (merge of deliver/J5/Sheaf.AlgebraicTopology.OrderedJoinCosetComparison)
