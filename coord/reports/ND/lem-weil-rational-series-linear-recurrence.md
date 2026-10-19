## Worker report

The module `Sheaf.RingTheory.RationalSeriesLinearRecurrence` states
`PowerSeries.isSolution_of_polynomial_mul_eq_polynomial`, with a single `sorry` proof.
It introduces no definitions or helper theorems and changes only the item's `lean` record.
No statement correction, new nodes, dependency repair, or disputed statement is needed.

The source read was the current `main-20261015` blueprint proof of
`prop-weil-rationality-criterion`, final paragraph (direction (1) implies (3)), and the
unit proof `sk-prop-criterion.proof.md`. The node records Milne, Lectures on Étale
Cohomology, II §27, proof of Lemma 27.9, p. 157, quoting Bourbaki IV.5 Exercise 3(a).
The theorem docstring carries all four coefficient-comparison steps of the DAG proof.

Clause-by-clause correspondence:

- A field `K` is `{K : Type u} [Field K]`, with explicit universe `u` and no
  characteristic assumption.
- The formal power series and its coefficient sequence are `(C : PowerSeries K)` and
  `fun n : ℕ ↦ PowerSeries.coeff n C`. No independent or arbitrary replacement sequence
  is introduced.
- The polynomials are `(P Q : Polynomial K)`.
- `Q(0) = 1`, equivalently `b₀ = 1`, is `(hQ : Q.coeff 0 = 1)`.
- `QC = P` in the power-series ring is
  `(hQC : (Q : PowerSeries K) * C = (P : PowerSeries K))`. Both casts use Mathlib's
  coefficient-preserving polynomial inclusion.
- The coefficients `bⱼ` are `Q.coeff j`; no redundant sequence of coefficients is bound.
- The prescribed order `d = max (deg Q) 1` is written everywhere as
  `max Q.natDegree 1`. The premise `hQ` ensures `Q ≠ 0`, so `natDegree` is exactly the
  nonnegative degree intended by the node; the maximum also ensures `d ≥ 1`.
- A nonnegative integer starting index is `(m : ℕ)`. Its precise, arbitrary vanishing
  condition is `(hP : ∀ N : ℕ, m + max Q.natDegree 1 ≤ N → P.coeff N = 0)`.
  This is not replaced by a stricter natural-degree inequality.
- For `i : Fin (max Q.natDegree 1)`, the node's coefficient `aᵢ = b_(d-i)` is
  `Q.coeff (max Q.natDegree 1 - (i : ℕ))`. Since `i < d`, this natural subtraction is
  the indicated positive index, with no truncation ambiguity.
- The conclusion uses the recorded `LinearRecurrence.IsSolution` interface. Its order
  is `max Q.natDegree 1`, its coefficients are
  `fun i : Fin (max Q.natDegree 1) ↦ -Q.coeff (max Q.natDegree 1 - (i : ℕ))`,
  and its sequence is `fun n : ℕ ↦ PowerSeries.coeff (n + m) C`.
  Unfolding `IsSolution` gives
  `c_(n+d+m) = ∑ i : Fin d, (-aᵢ) * c_(n+i+m)` for every `n : ℕ`.
  Moving the sum to the left, and writing the original index as `n+m`, gives exactly
  `c_(n+d) + ∑ i : Fin d, aᵢ * c_(n+i) = 0` for all original indices `n ≥ m`.
  The minus signs are Mathlib's right-side-sum convention, not a change in the
  node's recurrence coefficients. Every index at least `m` has this shifted form.
- The illustrative thresholds and constant-denominator parenthesis are specializations
  of these premises and conclusion. If `m = P.natDegree + 1`, then `N ≥ m+d`
  implies `N > P.natDegree`; if `P = 0`, `m = 0` satisfies `hP`. For `Q = 1`,
  `d = 1`, and the sole `i : Fin 1` is zero, so the coefficient is `-Q.coeff 1 = 0`.
  The conclusion is exactly `c_(n+1) = 0` for original indices `n ≥ m`.

Dependency declarations read in their source files and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs` (available through the
  imports), with its full class signature and docstring.
- `def-weil-formal-power-series`: `PowerSeries` and `PowerSeries.coeff`,
  `Mathlib.RingTheory.PowerSeries.Basic`.
- `def-weil-polynomial-ring`: `Polynomial`, `Mathlib.Algebra.Polynomial.Basic`;
  `Polynomial.natDegree`, `Mathlib.Algebra.Polynomial.Degree.Defs`.
- `def-weil-polynomial-as-power-series`: `Polynomial.coeToPowerSeries.ringHom`,
  `Polynomial.toPowerSeries`, and `Polynomial.coeff_coe`,
  `Mathlib.RingTheory.PowerSeries.Basic`. The coercion is the underlying function
  of that ring homomorphism, with identical coefficients.
- `def-weil-polynomial-coefficient`: `Polynomial.coeff`,
  `Mathlib.Algebra.Polynomial.Basic`.
- `def-weil-eventual-linear-recurrence`: `LinearRecurrence` and
  `LinearRecurrence.IsSolution`, `Mathlib.Algebra.LinearRecurrence`, applied exactly
  as the dependency's `mathlib_match.how` prescribes (negated coefficients and shifted
  sequence). Both the structure signature and the definition/docstring were read.

The two public imports supply all six statement dependencies and all five proof
 dependencies. There are no additional recorded proof modules to import.

Edge cases checked mathematically before writing:

- `Q = 1`: order one, zero recurrence coefficient, eventual coefficient vanishing,
  including constant nonzero `P` with the least admissible threshold `m = 0`.
- `P = 0, m = 0`: the normalized denominator is a power-series unit, so `C = 0`;
  all the stated recurrences hold. No `natDegree 0 < N` requirement was introduced.
- `P = Q = 1, C = 1, m = 0`: the degree-zero constant coefficient is unrestricted;
  the recurrence starts at `c₁ = 0`, not at `c₀ = 0`.
- Positive-degree denominators, missing intermediate coefficients, and `m = 0` with
  `deg P < d`: reversing the coefficients gives the intended order and no missing terms.
- A nonzero constant denominator normalized by `hQ` is necessarily `1`; `Q = 0`
  is excluded by the node's own premise. There is no order-zero or empty `Fin` case,
  because `max Q.natDegree 1 ≥ 1`.
- Fields of positive characteristic, including characteristic two, use the same
  additive-inverse convention and are all covered; the field universe is unrestricted.

Searches for an existing exact statement:

- `msearch.py ... leanfinder "linear recurrence coefficients of formal power series over a field"`:
  eight hits, including `LinearRecurrence.coeffs`, inverse-series coefficient formulas,
  and special analytic/Schroder series; none is this statement.
- `msearch.py ... leanfinder "If a polynomial Q with Q(0)=1 times a formal power series equals a polynomial P, the coefficients satisfy a linear recurrence beyond the support of P"`:
  eight hits: Hilbert-polynomial special series, `LinearRecurrence`/`IsSolution`/`coeffs`,
  inverse-series recursion, `charPoly`, and `mkSol`; no exact recurrence theorem.
- `msearch.py ... leansearch "The coefficients of a rational formal power series satisfy an eventual linear recurrence"`:
  eight hits, recurrence and power-series definitions plus an analytic binomial example;
  no exact theorem.
- `msearch.py ... loogle "LinearRecurrence.IsSolution PowerSeries.coeff Polynomial.coeff"`:
  zero hits (application-type-mismatch diagnostic for the combined names).
- `msearch.py ... loogle "PowerSeries.coeff_mul"`: one hit, the Cauchy-product formula;
  it is an ingredient, not the target statement.
- `msearch.py ... grep "LinearRecurrence|IsSolution|rational" RingTheory/PowerSeries`:
  zero hits.
- `rg` in upstream `WeilConjectures`, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the item id, recurrence/solution/power-series
  combinations, and the chosen declaration name found no exact statement or name clash.
  The upstream `WeilConjectures.ZetaLinearAlgebra.ShiftSpan` and
  `WeilConjectures.ZetaLinearAlgebra.RationalityCriterion` were read. In particular,
  `PowerSeries.sum_coeff_mul_coeff_eq_zero` requires `A.natDegree < n` and concludes
  a convolution with the denominator's natural degree, rather than preserving this
  node's arbitrary coefficient-vanishing threshold, specified positive order and
  specified reversed coefficients. The upstream rationality criterion supplies an
  existential recurrence, also different from this node. Neither is an exact attachment.

Validation: `scompile.py ND lem-weil-rational-series-linear-recurrence` on the delivered
module passed both sandbox and module-name compilation, with no errors or warnings.
All universes, types, indices and lambda binders are explicit. No proof was attempted.

## Second reading by ND

I reread the node statement, its source paragraph, all six dependency records, and the
candidate declaration independently. The source is the final paragraph of
`prop-weil-rationality-criterion.proof.md` (direction (1) implies (3)): from `QC=P`,
coefficient comparison above the numerator support gives the recurrence, with the separate
`Q=1` case. The Lean renders the objects and hypotheses as follows.

- The field is `{K : Type u} [Field K]`; `C : PowerSeries K` is the coefficient series,
  and `P Q : Polynomial K` are the numerator and normalized denominator.
- `hQ : Q.coeff 0 = 1` is exactly `Q(0)=1`; `hQC : (Q : PowerSeries K) * C =
  (P : PowerSeries K)` is the identity in `K[[T]]` through the coefficient-preserving
  polynomial inclusion.
- The degree/order is `max Q.natDegree 1`, matching `d=max(deg Q,1)` and ensuring
  an order at least one. The arbitrary threshold is `(m : ℕ)`, and
  `hP : ∀ N, m + max Q.natDegree 1 ≤ N → P.coeff N = 0` is precisely the required
  vanishing of numerator coefficients.
- The coefficients `a_i=b_(d-i)` are rendered by
  `-Q.coeff (d-i)` in the `LinearRecurrence` record. Mathlib's
  `LinearRecurrence.IsSolution` puts the coefficient sum on the right, so these
  negatives express `c_(n+d)+Σ a_i c_(n+i)=0`.
- The sequence passed to `IsSolution` is `fun n ↦ PowerSeries.coeff (n+m) C`, exactly
  the node's recurrence from index `m` on. The quantifier is the dependency's `∀ n : ℕ`.

The four proof clauses in the node are represented in the declaration docstring: support
of `Q` beyond `d`, coefficient comparison at `N=n+d`, reindexing `j=d-i`, and the
`m=deg P+1`, `P=0`, and `Q=1` edge cases. No hypothesis or conclusion clause is missing,
strengthened, or weakened, and no variable or universe is implicit.

Edge cases checked: `Q=1` gives order one and coefficient zero; `P=0,m=0` is allowed;
`P=Q=1` leaves `c₀` unrestricted and starts with `c₁=0`; `m=0`, positive-degree `Q`,
zero intermediate coefficients, and positive-characteristic fields (including
characteristic two) are covered. `max Q.natDegree 1` excludes an empty `Fin` order, as
required by the node.

Searches found no exact existing declaration. I searched the pinned Mathlib power-series
and linear-recurrence files for `PowerSeries`, `LinearRecurrence`, `IsSolution`, and
`rational`; searched upstream `WeilConjectures` and project `lean/Sheaf` for the theorem
name and for recurrence/power-series combinations; and reran semantic LeanSearch,
LeanFinder, and Loogle queries for a rational power-series recurrence. The only matches
were `LinearRecurrence.IsSolution` and convolution/degree ingredients. The upstream
`PowerSeries.sum_coeff_mul_coeff_eq_zero` has a fixed `A.natDegree < n` premise and does
not state this arbitrary-threshold, specified-order result.

No mismatch was found, so no source, statement, dependency, or module repair was needed.
The mandated `scompile.py` check passed for the module with no errors or warnings.

Independent search queries (second reader):

- LeanFinder: `A generating function annihilated to finite support by a normalized
  polynomial has eventually recurrent Taylor coefficients`: eight hits, including
  Hilbert polynomials, Laurent-series approximation and analytic-series results; none
  has this node's arbitrary normalized denominator and prescribed recurrence.
- Loogle: `"LinearRecurrence.IsSolution"`: one hit, the dependency definition itself.
- LeanSearch: `A normalized polynomial denominator for a generating function determines
  its linear recurrence coefficients after the numerator vanishes`: eight hits, mostly
  `RatFunc` numerator/denominator declarations and `LinearRecurrence.coeffs`; no match.
- `rg` in Mathlib `RingTheory/PowerSeries`, upstream `ZetaLinearAlgebra`, and project
  `lean/Sheaf/RingTheory`: no exact recurrence declaration. The nearby upstream
  `sum_coeff_mul_coeff_eq_zero` signature was opened and checked directly.

The Milne PDF was read via `pdftotext`: printed p. 157 quotes Bourbaki IV.5 Exercise 3,
part (a), for an arbitrary field; no characteristic or field-extension hypothesis applies
to the quoted rationality/recurrence fact. The surrounding extension `k ⊂ K` belongs to
Milne's descent Lemma 27.9, not this ingredient. This item cites no Stacks tag.
The sandbox node differs from the shared base only in `lean`, and its `lean.statement`
is verbatim equal to the declaration signature. There are no new/dependency modules,
statement changes, or repair notes to audit.
