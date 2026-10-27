## Worker report

The module `Sheaf.RingTheory.AdicEvaluationHomogeneousPreimages` states
`MvPowerSeries.exists_homogeneous_preimages_of_adic_evaluation`, with its whole
proof `sorry`. There are no definitions, helper claims, new nodes, dependency
repairs, or statement changes. The docstring includes all six steps of the DAG
proof, identifying the finite ideal-power expansion prerequisite explicitly.

Source read: `literature/stacks-project/dpa.tex`, Tag 09PZ,
`lemma-ci-well-defined`, especially the third proof paragraph adjoining variables
to make the lifted map surjective (the source says “some details omitted”).
The current blueprint's `lem-trf-local-term-locality.md` was also read; this node
is a supporting lemma beneath that unit, as its blueprint record states.

Hypotheses and clauses, in the order of the node:

| Node | Lean |
| --- | --- |
| Two commutative rings | `{C : Type u} {R : Type v} [CommRing C] [CommRing R]`; independent universes explicitly declared. |
| Ideal and adic completeness, including separatedness | `(I : Ideal R) [IsAdicComplete I R]`. |
| Coefficient ring homomorphism | `(f : C →+* R)`. |
| Nonnegative number of variables | `(s : ℕ)`, including zero. |
| Variables in the ideal | `(b : Fin s → R)` and `hb : ∀ j : Fin s, b j ∈ I`. |
| Generated ideal J | Every occurrence uses `Ideal.span (Set.range b)`. |
| Surjection C → R/J | `hf : Function.Surjective ((Ideal.Quotient.mk (Ideal.span (Set.range b))).comp f)`. |
| Given ring homomorphism E | `(E : MvPowerSeries (Fin s) C →+* R)`. No arbitrary replacement map or continuity assumption. |
| Reduction formula for every F and positive N | `hE` says `E F - MvPolynomial.eval₂ f b (F.truncTotal N) ∈ I ^ N` for all F, N with `1 ≤ N`. |
| Every z has polynomial corrections and a series | `∀ z : R, ∃ (H : ℕ → MvPolynomial (Fin s) C) (S : MvPowerSeries (Fin s) C), ...`. |
| Every correction has only degree-N nonzero monomials; zero allowed | `∀ N : ℕ, (H N).IsHomogeneous N`. This is Mathlib's support condition, not equality of totalDegree, so zero is allowed in every degree. |
| S_N is the sum of H_k for k<N | All partial sums are written literally as `∑ k ∈ Finset.range N, H k`; no auxiliary notion or let binder. |
| S_0=0 | `(∑ k ∈ Finset.range 0, H k) = 0`. This explicit clause is requested by the node. |
| Residual in J^N for every N≥0 | The first universally quantified residual conjunct, with exponent N and no positivity restriction. |
| Increment equals H_N for every N≥0 | The difference of the sums over `Finset.range (N + 1)` and `Finset.range N` equals `H N`. |
| Polynomials treated as series under E | `MvPolynomial.toMvPowerSeries` on the polynomial partial sum in both residual and tail clauses. |
| Compatible truncations | `∀ N : ℕ, S.truncTotal N = ∑ k ∈ Finset.range N, H k`; this includes N=0, as in proof step 4. |
| Tail evaluation in I^N for positive N | `∀ N : ℕ, 1 ≤ N → E S - E (MvPolynomial.toMvPowerSeries (...)) ∈ I ^ N`. |
| Exact preimage | `E S = z`. |
| In particular surjectivity | Final outer conjunct `Function.Surjective E`. |
| When s=0 positive-degree corrections can be zero | The chosen witness also satisfies `s = 0 → ∀ N : ℕ, 0 < N → H N = 0`. |

`F.truncTotal N` keeps exactly exponents of total degree less than N, by
`MvPowerSeries.coeff_truncTotal_eq_ite`; evaluating this polynomial with
`MvPolynomial.eval₂ f b` is exactly the finite sum in the hypothesis.
`MvPolynomial.eval₂_eq'` identifies its monomial factors with the product over
`Fin s`. Thus no analytic convergence or stronger substitution API is assumed.

Dependency declarations used and read in full:

- `def-weil-pbc-adically-complete-ring`: the recorded
  `Mathlib.RingTheory.AdicCompletion.Basic`, `IsAdicComplete`. Its definition
  extends `IsHausdorff I R` and `IsPrecomplete I R`; it is the node's ring notion.
- `def-weil-pbc-multivariate-power-series`: the recorded
  `Mathlib.RingTheory.MvPowerSeries.Basic`, `MvPowerSeries`, applied to `Fin s`
  and C. This is the coefficient-family construction with the standard ring
  operations. It is publicly imported through `Mathlib.RingTheory.MvPowerSeries.Trunc`.
- Supporting Mathlib interfaces read: `MvPowerSeries.truncTotal` in
  `Mathlib.RingTheory.MvPowerSeries.Trunc`, `MvPolynomial.toMvPowerSeries` in
  `Mathlib.RingTheory.MvPowerSeries.Basic`, `MvPolynomial.IsHomogeneous` in
  `Mathlib.RingTheory.MvPolynomial.Homogeneous`, and `MvPolynomial.eval₂` in
  `Mathlib.Algebra.MvPolynomial.Eval` (available through the homogeneous import).
- The proof-only prerequisite `lem-trf-finite-support-monomial-ideal-power` has
  no Lean record or upstream audit declaration in the node read. No module can
  be imported for it yet. Its use is preserved in the proof docstring; the
  maintainer can add its proof import when that prerequisite is stated.

Edge cases checked mathematically: N=0 gives J^0=R, an empty partial sum, and a
constant homogeneous correction. `s=0` has one exponent vector (degree zero),
J=0, and the quotient surjection supplies a constant preimage; all positive
corrections are zero. J=0 with nonempty variables works the same way using
constant preimages. Zero corrections satisfy IsHomogeneous at every degree.
Nilpotent I requires no change. Both rings may be zero rings; no Nontrivial,
Noetherian, local-ring, characteristic, or injectivity hypothesis is added.
For I=R, completeness forces R to be the zero ring, which is still included.

Searches for an exact existing statement:

- `msearch.py ... leanfinder`: “A power series evaluation into an adically
  complete ring has homogeneous polynomial corrections and a series preimage
  when coefficients surject modulo the variable ideal”. Eight hits, concerning
  Weierstrass division and its coefficient sequences; no exact match.
- `msearch.py ... loogle`: `MvPowerSeries.truncTotal, MvPolynomial.IsHomogeneous`.
  Zero hits.
- `msearch.py ... grep`: `truncTotal|IsHomogeneous|surjective_of_mk_map_comp_surjective`
  in RingTheory. Twenty-five hits: truncation/homogeneous interfaces and abstract
  surjectivity are ingredients, not the full witness statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for homogeneous preimages,
  adic homogeneous evaluation, truncTotal and the proposed declaration name;
  exact item-id grep in `lean/WeilConjectures`; exact-name/concept search in
  `dag/lean_names_upstream.json` and Mathlib. No full existing statement found.
  The read upstream `PowerSeriesAdicEvaluation` provides existence and uniqueness
  of E; `PowerSeriesOntoCompletion` constructs a map to an adic completion.
  Neither gives this theorem for the prescribed coefficient map and E with all
  the required correction and truncation clauses. Mathlib's
  `surjective_of_mk_map_comp_surjective` gives only surjectivity under a different
  map/completeness interface, not the homogeneous witnesses.

No statement fault or STATEMENT-DISPUTED issue found. Only the item's `lean`
field was added; its statement, dependency lists, proof and all other fields
are unchanged. All variables are bound explicitly and `autoImplicit` is false.
The server single-file compile and the delivery dry run are the validation steps.

## Second reading by Q130

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
