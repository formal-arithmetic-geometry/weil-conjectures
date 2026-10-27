## Worker report

The module `Sheaf.Algebra.MvPolynomial.BoundedLinePolynomialInterpolation` states
`MvPolynomial.exists_of_bounded_affine_lines`. Its sole proof is `sorry`; no definitions,
additional theorems, or new nodes were needed. The node changes only in `lean`.

Hypothesis and clause correspondence:

- The infinite field is `{K : Type u} [Field K] [Infinite K]`.
- The vector space is `{W : Type v} [AddCommGroup W] [Module K W]`. Its universe is
  independent of the field's universe; no finite-dimensionality assumption is imposed.
- The nonnegative integer bound is `(D : ℕ)`, exactly the nonnegative integers in the node.
- The function is `(F : W → K)`.
- Every pair of vectors is covered by `∀ v w : W` in `hF`. The polynomial is
  `∃ q : Polynomial K`; its bound is `q.natDegree ≤ D`, and its values are prescribed
  by `∀ t : K, F (t • v + w) = q.eval t`. Using natural degree allows the zero
  polynomial, including when D = 0, just as the recorded polynomial-ring node permits.
- Every nonnegative number of coordinates and every tuple of vectors is covered by
  `∀ (r : ℕ) (e : Fin r → W)`. Indexing by `Fin r` merely renumbers 1,...,r.
- The representing polynomial is `∃ P : MvPolynomial (Fin r) K` and its bound is
  `P.totalDegree ≤ D`, not a separate-variable degree bound.
- Agreement at every coordinate tuple is
  `∀ x : Fin r → K, F (∑ i : Fin r, x i • e i) = MvPolynomial.eval x P`.
- The second conjunct renders the final determination clause: for every r and every
  P,Q, equality of evaluations at every `x : Fin r → K` implies `P = Q`. This clause
  has no degree restriction and does not restrict P,Q to the representing polynomial.

Dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs. Its `mathlib_match` supplies
  the field class directly; there is no missing Lean record to repair.
- `def-weil-polynomial-ring`: `Polynomial`, Mathlib.Algebra.Polynomial.Basic;
  `Polynomial.natDegree`, Mathlib.Algebra.Polynomial.Degree.Defs; and `Polynomial.eval`,
  Mathlib.Algebra.Polynomial.Eval.Defs. The evaluation module is imported publicly.
- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial`, Mathlib.Algebra.MvPolynomial.Basic;
  `MvPolynomial.aeval`, Mathlib.Algebra.MvPolynomial.Eval; and `MvPolynomial.algHom_ext`,
  Mathlib.Algebra.MvPolynomial.Basic. The statement uses the same ring and its direct
  evaluation `MvPolynomial.eval`. The total degree is Mathlib's `MvPolynomial.totalDegree`
  from Mathlib.Algebra.MvPolynomial.Degrees.
- Proof imports are Mathlib.LinearAlgebra.Lagrange (`Lagrange.eq_interpolate`,
  `Lagrange.interpolate_eq_sum`, node lem-sfb-lagrange-reconstruction),
  Mathlib.Algebra.Polynomial.Roots (`Polynomial.eq_of_infinite_eval_eq`, node
  lem-trf-polynomial-infinite-evaluation-identity), and Mathlib.Algebra.MvPolynomial.Funext
  (`MvPolynomial.funext_set`, node lem-trf-infinite-field-top-form-direction).
  These are plain imports, as required for the proof plan. No dependency interface was replaced.

Source and edge-case checks:

Read Milne, Abelian Varieties, Chapter I, Lemma 10.12 and its proof on printed p.47,
with Proposition 10.13 and its proof on pp.47-48, using the repository PDF. Milne's
translated-coordinate induction applies to arbitrary tuples, rather than only independent
ones. The DAG supplies the uniform bound explicitly; its four-step bounded interpolation,
determination, and top-degree argument are included in the declaration docstring.

For r = 0 the sum is zero and the polynomial ring in no variables is K; use the constant
F(0). Its sole evaluation determines that constant. D = 0 permits constant and zero
polynomials, with both natural degree and total degree zero. The zero space W is allowed.
Repeated, zero, and linearly dependent e_i are allowed: there is no independence binder.
Zero restrictions on lines are permitted. No characteristic assumption or condition D <
char(K) is present or needed: Lagrange uses distinct points, not division by factorials,
and the top-degree contradiction uses infinitude, including in positive characteristic.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder`, query: "A function on a vector space over an infinite field
  with polynomial restrictions of degree at most D on every affine line is a polynomial
  of total degree at most D in finite coordinates". Eight hits, including
  ChevalleyThm.MvPolynomialC.degBound, MvPolynomial.map_restrict_dom_evalₗ,
  MvPolynomial.schwartz_zippel_totalDegree, and Polynomial.exists_eq_polynomial.
  None states the bounded affine-line criterion.
- `msearch.py ... loogle`, query: "MvPolynomial.funext, Polynomial.natDegree".
  Successful search, zero hits.
- `msearch.py ... leansearch`, query: "Polynomial on every affine line with a uniform
  degree bound implies multivariate polynomial of bounded total degree". Eight hits:
  MvPolynomial.totalDegree, MvPolynomial.aeval_natDegree_le,
  MvPolynomial.IsHomogeneous.totalDegree_le, ChevalleyThm.MvPolynomialC.degBound,
  MvPolynomial.restrictTotalDegree, MvPolynomial.totalDegree_le_degrees_card,
  MvPolynomial.degreeOf, MvPolynomial.IsHomogeneous. These provide notions or
  ingredients; none states the criterion.
- `msearch.py ... grep`, query: `polynomial.*line|line.*polynomial|IsPolynomial|isPolynomial`,
  restricted to Algebra/MvPolynomial. Seven hits in Coeff, Basic and Derivation concern
  linear combinations, linear maps and derivations, rather than the criterion.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for bounded-line, line/polynomial,
  and finite-coordinate terminology found unrelated polynomial geometry and finite
  coordinate constructions, not this statement. `grep -rn` for the exact node id in
  `lean/WeilConjectures` found none. Searching the proposed declaration name in
  Mathlib, both project roots, and `dag/lean_names_upstream.json` found no collision.

Validation: scompile.py compiled both its sandbox view and the final library module
cleanly. The initial compile identified that univariate evaluation needed a public import;
adding Mathlib.Algebra.Polynomial.Eval.Defs resolved it. Explicit universes and
`set_option autoImplicit false` prevent automatic binders. Maximum line width is 95.
No statement correction, disputed statement, missing notion, or dependency fault was found.

## Second reading by Q142

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
