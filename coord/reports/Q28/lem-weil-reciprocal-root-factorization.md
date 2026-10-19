## Worker report

The module `Sheaf.Algebra.Polynomial.ReciprocalRootFactorization` states
`Polynomial.reciprocal_root_factorization`, with `sorry` as its only proof. No definitions,
auxiliary theorems, new nodes, dependency repairs, or statement corrections are needed.
The node copy changes only `lean`.

Source read: the node's seven-step proof and
`literature/blueprint/master/blueprint/sec-zeta-weil/sk-def-roots/def-weil-ordinary-reciprocal-roots.md`,
order 2859. That source states the nonvanishing of ordinary roots and the product of
`1 - α_j T` over reciprocal roots with algebraic multiplicity. This helper generalizes the
coefficient field as already specified by its DAG statement; it does not import the source's
unneeded geometric objects. The helper has no `blueprint_update` or repair note.

Hypothesis and object correspondence:

- The arbitrary fields are `{K : Type u} [Field K]` and `{L : Type v} [Field L]`, with
  independent explicit universes. Algebraic closedness is `[IsAlgClosed L]`. No algebraicity
  of `L/K` is assumed: the node allows every algebraically closed receiving field.
- The specified coefficient homomorphism is `(ι : K →+* L)`. Injectivity follows from the
  field structures; it is not added as a hypothesis.
- The polynomial is `(P : K[X])`, and its constant-term hypothesis is
  `(h0 : P.eval 0 = 1)`. There is no extra nonzero or positive-degree assumption.
- `P.map ι` is exactly `P_L`. Its `IsRoot β` means `(P.map ι).eval β = 0`, equivalently
  `P.eval₂ ι β = 0`, so evaluations agree with the node's convention for `P(x)` in `L`.
- `P.natDegree` is the node's natural number `r`; the hypothesis excludes `P = 0`.
  Indices `Fin P.natDegree` enumerate exactly `r` factors, with zero-based indices in place
  of the paper's one-based indices. Their cardinality is `r`, including when `r = 0`.

Conclusion correspondence, clause by clause:

1. `(∀ β : L, (P.map ι).IsRoot β → β ≠ 0)` states that every root is nonzero.
   `Set.BijOn (fun β : L ↦ β⁻¹) {β | (P.map ι).IsRoot β}
   {α | α ≠ 0 ∧ (P.map ι).IsRoot α⁻¹}` states the specified bijection, with precisely
   the inverse operation, rather than an arbitrary bijection. The target set is the
   node's reciprocal roots, viewed as the nonzero subset of `L`; over a field this is
   canonically the same as the units satisfying the inverse-root predicate.
2. `∃ α : Fin P.natDegree → Lˣ, P.map ι = ∏ j, (1 - C (↑(α j) : L) * X)` is the exact
   product factorization in `L[X]`. Using `Lˣ` makes nonvanishing of every factor parameter
   part of its type, without an added premise.
3. The last universal conjunct applies to EVERY unit family giving this factorization.
   For each `a : Lˣ`, `Fintype.card {j : Fin P.natDegree // α j = a}` is the number of its
   occurrences, and is asserted equal to `rootMultiplicity (↑a⁻¹ : L) (P.map ι)`.
   The next equality identifies this with
   `rootMultiplicity (↑a : L) (P.map ι).reverse`, the multiplicity in `P_L^#`.
   The factor-family quantifier is outside these equalities, so they characterize all
   factorizations, not just one chosen factorization.
   `(∃ j, α j = a) ↔ (P.map ι).IsRoot (↑a⁻¹ : L)` explicitly states that the factors
   contain exactly the reciprocal roots. The multiplicity equality supplies their
   algebraic multiplicities. The final conjunct gives, for every other factor family
   `α'`, a permutation `σ : Equiv.Perm (Fin P.natDegree)` satisfying
   `∀ j, α' j = α (σ j)`, the stated uniqueness up to reordering.
   The total number with multiplicity is exactly `P.natDegree`: there is one occurrence
   for each member of `Fin P.natDegree`; no indexing length is left existential or
   unconstrained. Thus the node's final counting clause is built into the family type.

Dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs` (extends a commutative ring with
  division and nontriviality).
- `def-weil-algebraic-closure`: `IsAlgClosed`,
  `Mathlib.FieldTheory.IsAlgClosed.Basic`, whose docstring identifies splitting of all
  polynomials with having a root for every nonconstant polynomial. Its `IsAlgClosure`
  and `AlgebraicClosure` interfaces were also read; they impose algebraicity not required
  here, so the statement correctly uses `IsAlgClosed` only.
- `def-weil-polynomial-ring`: `Polynomial`, `Mathlib.Algebra.Polynomial.Basic`;
  `natDegree` in `Mathlib.Algebra.Polynomial.Degree.Defs`.
- `def-weil-polynomial-root`: `Polynomial.eval₂` and `Polynomial.IsRoot`,
  `Mathlib.Algebra.Polynomial.Eval.Defs`.
- `def-weil-root-multiplicity`: `Polynomial.rootMultiplicity`,
  `Mathlib.Algebra.Polynomial.Div` (the largest dividing power, with value zero for the
  zero polynomial).
- `def-weil-polynomial-coefficient`: `Polynomial.coeff` in
  `Mathlib.Algebra.Polynomial.Basic`, and `leadingCoeff` in the degree definitions.
- `lem-weil-reciprocal-polynomial`:
  `Polynomial.reciprocal_polynomial_of_constantCoeff_one` in
  `Sheaf.Algebra.Polynomial.ReciprocalPolynomial`. Its full source and proof docstring
  were read. The statement uses its very same `Polynomial.reverse` construction;
  no second definition of reciprocal polynomial is introduced.

The proof dependencies were read as well: the degree-preserving and coefficient formulas
in `Mathlib.Algebra.Polynomial.Degree.Lemmas` and `Eval.Coeff`,
`Polynomial.Splits.eq_prod_roots` in `Mathlib.Algebra.Polynomial.Splits`,
`Polynomial.rootMultiplicity_mul` in `Mathlib.Algebra.Polynomial.RingDivision`,
`Polynomial.rootMultiplicity_pos` in `Mathlib.Algebra.Polynomial.Div`, and
`Polynomial.reflect_mul` in `Mathlib.Algebra.Polynomial.Reverse`.
The public imports supply the notions and the already recorded reciprocal-polynomial
statement; the non-public `RingDivision` import supplies the multiplicity product proof
step. The other Mathlib proof interfaces are already exposed through these imports.
The declaration docstring records all seven proof steps and their DAG dependencies.

Edge cases checked:

- `P = 1`: degree zero, no roots, empty inverse-root sets, empty product one, all counts
  zero, and the permutation of `Fin 0` covers uniqueness. No positive-degree premise.
- `P = 0`: excluded by `P.eval 0 = 1` in a field, so the node's use of ordinary natural
  degree and finite multiplicities is justified.
- Repeated roots: over any characteristic, `(1 - a X)^m` with nonzero `a` has `m`
  repeated entries; the subtype cardinality records these repetitions. No separability
  or distinctness is assumed.
- Zero is excluded from reciprocal roots exactly as in the node. Ordinary roots use all
  of `L`, and the theorem itself proves their nonvanishing.
- The map `ι` need not be surjective and `L/K` need not be algebraic. Neither condition
  was added. The statement also covers `K = L` with the identity homomorphism.
- The reciprocal of `P = 1` is one, so its multiplicity clause remains valid at degree zero.

Searches actually run:

- `msearch.py`, leanfinder: “A polynomial with constant coefficient one over a field
  factors over an algebraically closed extension as a product of one minus reciprocal
  root times X, with root multiplicities”. Eight hits: algebraic-closure construction,
  `IsAlgClosed.splits`, ordinary products over roots, and separable finset factorization;
  none states all clauses of this node.
- `msearch.py`, loogle: `Polynomial.reverse, Polynomial.rootMultiplicity,
  Polynomial.Splits.eq_prod_roots`. Zero hits.
- `msearch.py`, grep: `reciprocal|roots_reverse|rootMultiplicity.*reverse` in
  `Algebra/Polynomial`. Zero hits reported by the wrapper.
- Direct `rg` of the upstream `WeilConjectures` and project `lean/Sheaf` for
  `reciprocal|Reciprocal|rootMultiplicity.*reverse|roots_reverse`: read the relevant
  upstream `WeilConjectures.Mathlib.Algebra.Polynomial.Splits` module in full. Its
  `Polynomial.eq_prod_one_sub_inv_roots` proves the product identity for a split
  polynomial over its root multiset, but does not state the bijection, uniqueness or
  the reciprocal-polynomial multiplicity clauses. Read
  `Polynomial.roots_reverse_of_monic` in `WeilConjectures.ZetaLinearAlgebra.Pairing`;
  it assumes monicity and states a multiset identity, not this node's full statement
  for arbitrary constant-term-one polynomials. Neither is an exact existing binding.
- `grep -rn 'lem-weil-reciprocal-root-factorization'` in upstream `WeilConjectures`:
  no hits. `rg` for reciprocal names in `dag/lean_names_upstream.json`: no hits.
- Direct `rg` for the new declaration name `reciprocal_root_factorization` across
  Mathlib, upstream `WeilConjectures`, and `lean/Sheaf`: no collision.

No statement dispute or node fault was found. Compilation and delivery preflight results
are recorded below after the required wrapper checks.

Validation: `scompile.py Q28 lem-weil-reciprocal-root-factorization` compiled the
single delivered module successfully, both in the sandbox and at its library module path,
against the reciprocal-polynomial dependency overlay. No errors or warnings were emitted.
The Lean file has no line longer than 100 characters. All universes and variables are
explicitly bound; `open Classical in` supplies decidability for the finite occurrence counts
without an extra statement hypothesis, as in the project's example module.

## Second reading by Q28

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
