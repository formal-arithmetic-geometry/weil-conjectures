## Worker report

The module `Sheaf.RingTheory.StandardGradedCumulativeDimension` states
`GradedAlgebra.IsStandard.ringKrullDim_eq_natDegree_cumulative`, with its sole proof
`sorry`. No notions are defined anew. Only the item's `lean` field changes.

Source read: `literature/stacks-project/algebra.tex`, lines 28401–28441,
Tag 00P6, `lemma-dimension-graded`, statement (3) and proof. Its degree-piece
polynomial has degree one less than the cumulative polynomial, except when the
piece polynomial vanishes: then the cumulative polynomial is a positive constant.
The node explicitly retains that case, and the Lean conclusion does too.

Hypothesis and clause correspondence:

- Field `k`: `{k : Type u} [Field k]`.
- Commutative `k`-algebra `S`: `{S : Type v} [CommRing S] [Algebra k S]`.
  The universes `u` and `v` are independent and explicitly declared.
- Direct-sum grading in nonnegative degrees: `(𝒜 : ℕ → Submodule k S)` and
  `[GradedAlgebra 𝒜]`. This is the dependency's actual unbundled grading interface.
- Standard grading, with finitely many degree-one generators: `[IsStandard 𝒜]`.
  Its fields are `(𝒜 1).FG` and `Algebra.adjoin k (𝒜 1 : Set S) = ⊤`.
- Degree zero is `k`: the recorded theorem
  `GradedAlgebra.IsStandard.grade_zero_eq_one` gives `𝒜 0 = 1`, where the unit
  submodule is the scalar image. `[Nontrivial S]` ensures that the field maps
  injectively into `S`, so this image is a copy of `k`, exactly the node's
  `S₀ = k`. This does not exclude a ring permitted by that hypothesis: a ring
  whose degree-zero piece is a field cannot be the zero ring. No domain,
  reducedness, algebraic closure, characteristic, or positive dimension is assumed.
- Each graded piece is finite-dimensional: supplied by the recorded instance
  `GradedAlgebra.IsStandard.finite_grade`; no independent finiteness assumption
  is necessary. Thus `Module.finrank k (𝒜 j)` is the actual dimension.
- Nonzero rational polynomial: `(Q : Polynomial ℚ) (hQ : Q ≠ 0)`.
- Integer threshold at least one: `(N : ℕ) (hN : 1 ≤ N)`. All integers above
  that positive threshold are naturally nonnegative, so using natural indices
  gives exactly the asserted quantification.
- Equality for every `n ≥ N`: `hpoly : ∀ n : ℕ, N ≤ n → Q.eval (n : ℚ) =
  ∑ j ∈ Finset.range n, (Module.finrank k (𝒜 j) : ℚ)`.
  `Finset.range n` contains precisely `0, ..., n-1`; the dimensions are summed
  in the rationals for comparison with the rational polynomial's evaluation.
- Finite Krull dimension equal to the degree: `ringKrullDim S =
  (Q.natDegree : WithBot ℕ∞)`. A natural number cast is neither infinity nor
  bottom, and `hQ` makes `natDegree` the degree of the nonzero polynomial.
- Eventually zero pieces: `∃ D : ℕ, ∀ j : ℕ, D ≤ j → 𝒜 j = ⊥`.
  A zero submodule is exactly the vanishing of that graded piece.
- In that case a positive constant polynomial and dimension zero: the second
  conjunct concludes `∃ c : ℚ, 0 < c ∧ Q = Polynomial.C c ∧ ringKrullDim S = 0`.
  It is conditional; the theorem never assumes eventual vanishing.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (definition and docstring).
- `WeilConjectures.RingTheory.GradedAlgebra.Standard`: `GradedAlgebra.IsStandard`,
  `GradedAlgebra.IsStandard.grade_zero_eq_one`, `grade_eq_pow`, and `finite_grade`
  (full definitions/signatures and docstrings, lines 80–140).
- `Mathlib.LinearAlgebra.Dimension.Finrank`: `Module.finrank` (lines 49–66).
- `Mathlib.Algebra.Polynomial.Basic`: `Polynomial` (lines 68–76), with
  `Polynomial.natDegree` in `Mathlib.Algebra.Polynomial.Degree.Defs` (lines 48–53).
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim` (lines 26–32).

The public imports provide the statement's notions. Plain imports retain the
already stated proof dependencies:
`Mathlib.RingTheory.Localization.AtPrime.Basic` (`Localization.AtPrime`),
`Mathlib.RingTheory.Localization.Submodule` (`IsLocalization.isNoetherianRing`),
`Mathlib.RingTheory.FiniteType` (`Algebra.FiniteType.isNoetherianRing`),
`Mathlib.Algebra.Polynomial.Roots` (`Polynomial.eq_of_infinite_eval_eq`), and
`Sheaf.RingTheory.HilbertSamuelGrowthDimension`
(`IsLocalRing.exists_hilbertSamuel_polynomial`). Their signatures were read.
The vertex-dimension and maximal-adic length-bridge nodes have no recorded
Lean statement in the read clone and supply no objects needed to type this
statement; their proof plans remain cited by node id in the theorem docstring.
No proof prerequisite was imposed as an extra hypothesis.

Searches actually run through `msearch.py`, group Q04, this item:

- LeanFinder: “The Krull dimension of a standard graded algebra equals the
  degree of its cumulative Hilbert polynomial”. Eight results: polynomial-ring
  dimension formulas, KrullDimLE, and support dimension. No exact match.
- Loogle: `"ringKrullDim", "Hilbert"`. Zero hits.
- Grep: `hilbert.*(dimension|krull)|krull.*hilbert|dimension.*hilbert`,
  in Mathlib/RingTheory. Zero hits.
- LeanSearch: “The degree of the cumulative Hilbert polynomial of a standard
  graded algebra equals the Krull dimension”. Eight results, including
  `Polynomial.hilbertPoly`, polynomial-ring dimension formulas, `ringKrullDim`,
  maximal-ideal height, and `Ideal.sup_height_eq_ringKrullDim`. None identifies
  cumulative Hilbert growth with dimension for arbitrary standard graded rings.

Local searches actually run: `grep -rn` for this node id in
`lean/WeilConjectures` (no result), and `rg -n` for cumulative/Hilbert/dimension
combinations in `lean/WeilConjectures` and `lean/Sheaf`. The existing
`StandardGradedHilbertFunction` gives eventual polynomiality, not the degree
or dimension identification. `ProjectiveConeHilbertStandardDegrees` and
`JetDiagramHilbertControl` discuss cumulative functions without this theorem.
Projective Hilbert-polynomial results use projective schemes and do not state
this affine graded-ring assertion. No existing declaration matched.
There is no repair note for this item.

Edge cases checked mathematically before writing:

- `S = k`, no degree-one generators: cumulative sum is 1 for `n ≥ 1`, so
  `Q = 1`, degree and dimension zero, and the second conjunct applies.
- `S = k[t]`: the cumulative sum is `n`; degree and dimension are one.
- `S = k[x,y]`: cumulative sum is `n(n+1)/2`; degree and dimension are two.
- `S = k[t]/(t^r)`, `r ≥ 1`: for `n ≥ r` the sum is `r`; nilpotents are
  permitted, the constant is positive, and dimension is zero.
- `S = k[x,y]/(xy)`: sum is `2n-1` for `n ≥ 1`, degree and dimension one;
  no domain assumption has slipped in.
- Finite fields and positive characteristic cause no change: coefficients
  and evaluations are rational dimension counts, not evaluations in `k`.
- `N = 1` is allowed, `n = 0` is outside the claimed range, and `D = 0`
  would force `S₀ = 0`, so is incompatible with the standard nonzero algebra.
- The zero polynomial is explicitly excluded; the zero ring is excluded by
  `S₀ = k`, as reflected by `Nontrivial S`.

No statement correction, new node, dependency module, or mathematical dispute.
The server `scompile.py` compiled the sandbox and final library module cleanly
(5.2 s and 1.2 s); the only proof is the expected `sorry`.

## Second reading by Q04

This is the author's separate second reading, not a claim of an independent
agent review; the dispatcher prohibits starting agents and the maintainer
provides the independent delivery review. I re-opened the node and the complete
Lean signature. The grading and standardness use the recorded class, whose
finite-grade instance justifies every finrank. Nontriviality expresses the
node's field copy in degree zero. The threshold uses `≥ 1`; the sum stops at
`n-1`, with no off-by-one shift. The equality is in `WithBot ℕ∞` against a
finite natural degree. The eventual-vanishing clause remains an implication,
with strict positivity and a genuine constant-polynomial equality, and includes
the dimension-zero conclusion. The proof docstring follows all six node steps,
including the denominator argument in degree zero and polynomial identity.
No mismatches were found, and no node statement was changed.
