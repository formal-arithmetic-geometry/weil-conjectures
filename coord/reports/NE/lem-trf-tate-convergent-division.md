## Worker report

The module `Sheaf.RingTheory.TateConvergentDivision` states
`RestrictedSeries.exists_bounded_division`, with its sole proof `by sorry`.
It adds no definition, instance, axiom, or other theorem. The existing node is
unchanged except for its `lean` record.

Clause-by-clause correspondence:

- A field complete for a real-valued nonarchimedean absolute value is
  `(K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]`.
  `NormedField` extends `Field`, has a multiplicative real norm, and its distance
  is the distance induced by that norm. Unlike `NontriviallyNormedField`, it
  permits the trivial absolute value. No characteristic restriction is imposed.
- The nonnegative integers `s,t` are `(s t : ℕ)`, without positivity assumptions.
  The variables and divisor list are indexed by `Fin s` and `Fin t`.
- The ring `T_s` is exactly
  `MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin s ↦ (1 : ℝ))`,
  used in the recorded dependency. Its coefficients tend to zero along the
  cofinite filter. Its multiplication is the formal finite Cauchy product.
  Every `b i`, `f`, `q i`, and `r` belongs to this same subring.
- The Gauss norm is Mathlib's `MvPowerSeries.gaussNorm (norm : K → ℝ)
  (fun _ : Fin s ↦ 1)`. The radius weights are all one, so its defining
  supremum is exactly the supremum of coefficient absolute values.
- `hb : ∀ i : Fin t, ... (b i).val = 1` is the entire divisor hypothesis.
  There is no Gröbner-basis, domain-of-coefficients, or extra leading-term
  hypothesis. Nonvanishing of each divisor follows from this norm condition.
- Instead of introducing a separate partial leading-exponent function, the
  conclusion existentially supplies `β : Fin t → (Fin s →₀ ℕ)` and gives its
  complete graph: `AchievesGaussNorm ... (β i)` and, for every other achieving
  exponent `μ`, `toDegLex μ ≤ toDegLex (β i)`. Thus `β i` is precisely `L(b_i)`.
  `AchievesGaussNorm` is Mathlib's existing coefficient-maximum predicate;
  `toDegLex` uses its existing graded lexicographic linear order. The order
  compares total degree and then the usual lexicographic order on the ordered
  coordinates `Fin s`, giving priority to the first differing coordinate.
  The characterization determines `β i` uniquely by antisymmetry. Existence
  is a consequence of the node's hypotheses (the finite nonempty maximum set
  from restrictedness), so this is an expansion of the node's internal
  definition of `L`, not a strengthened division assertion or a new assumption.
- The decomposition is `f = (∑ i : Fin t, q i * b i) + r` in the subring.
  The parentheses explicitly put `r` outside the finite sum.
- `(∀ i : Fin t, gaussNorm ... (q i).val ≤ gaussNorm ... f.val)` gives each
  quotient bound; the next conjunct gives `gaussNorm ... r.val ≤ ... f.val`.
- `∀ ν : Fin s →₀ ℕ, MvPowerSeries.coeff ν r.val ≠ 0 →
  ∀ i : Fin t, ¬ β i ≤ ν` is exactly the required support exclusion.
  Here the unwrapped `Finsupp` order is componentwise, distinct from the
  `toDegLex` order in the characterization of `β`.
- The empty-list assertion `r=f` follows directly from the same decomposition
  at `t=0`, because the empty sum is zero. No redundant extra conjunct is needed.

Dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs, read its signature and
  the inheriting `NormedField` signature in Mathlib.Analysis.Normed.Field.Basic.
- `def-trf-restricted-series-presentation`:
  `Sheaf.RingTheory.RestrictedSeriesPresentation`, including the full signatures
  and docstrings of `RestrictedSeries.constants`,
  `RestrictedSeries.IsTopologicallyFinitelyPresented`,
  `RestrictedSeries.IsAffinoidQuotient`, and
  `RestrictedSeries.HasBoundedTopologicallyGeneratedImage`. This dependency
  already uses the Mathlib restricted subring and Gauss norm, which this module
  reuses verbatim. It is publicly imported; the adic and affinoid predicates
  themselves impose no additional hypotheses on this theorem.
- Underlying Mathlib interfaces: `MvPowerSeries.IsRestricted`, its protected
  `subring`, `MvPowerSeries.gaussNorm`, `MvPowerSeries.AchievesGaussNorm`,
  `Finsupp.DegLex.le_iff`, and `MonomialOrder.degLex`.
- Proof dependency `lem-trf-unit-leading-ring-polynomial-division` is the
  Mathlib match `MonomialOrder.div`, Mathlib.RingTheory.MvPolynomial.Groebner,
  whose complete signature and proof context were read. Its module is imported
  without `public`, as a proof dependency.
- Proof dependency `lem-trf-restricted-series-gauss-completion` has no Lean
  record or Mathlib match on the read base. No import can yet be given for it.
  The docstring retains its role in the proof plan; this node is not needed
  to type the statement, and no completeness or regrouping theorem is restated.

Edge cases checked mathematically before writing: `t=0` gives `r=f` with vacuous
quotient and support constraints; `s=0` leaves the unique exponent zero and the
ring of constants. For `s=0,t>0`, divide by one norm-one constant and take `r=0`.
For `f=0`, all quotients and the remainder can be zero. A constant unit divisor
forces zero remainder. Trivial absolute values make restricted series
polynomials, so ordinary polynomial division applies. No step requires a
discrete value group, a nontrivial absolute value, or a residue characteristic.
For `b=X-a` with `|a|<1` and `f=X`, `β=1`, `q=1`, and `r=a` satisfy every clause.
For equal-degree exponents, Mathlib's `degLex_single_lt_iff` confirms that the
earlier coordinate has priority. For remainder divisibility, ordinary
`Finsupp.le` compares every coordinate, rather than comparing total degrees.

Searches for an existing statement (all via prescribed msearch.py):

- LeanFinder, `Bounded division of restricted multivariate power series by a
  finite family in a complete nonarchimedean field with Gauss norm bounds and
  remainder outside leading monomial multiples`: eight hits, all formal
  univariate Weierstrass division interfaces; no exact match.
- LeanSearch, `Restricted multivariate power series admit division by a finite
  list with Gauss norm bounded quotients and a reduced remainder`: eight hits,
  principally Weierstrass division and `MonomialOrder.div`. The latter is
  polynomial division without analytic convergence or the Gauss norm bounds.
- Loogle, `"IsRestricted", "div"`: zero hits.
- Mathlib grep, `division|div_rem|remainder`, RingTheory/MvPowerSeries: one
  irrelevant coefficient-map theorem in Basic.lean.
- Additional LeanSearch/LeanFinder searches for the largest graded-lex
  Gauss-maximum exponent found `lexOrder`, `weightedOrder`, `order`, and
  univariate Gauss norms. Those use minimum support orders or do not choose a
  leading exponent. Mathlib grep `leading|Leading|AchievesGaussNorm` in
  RingTheory/MvPowerSeries found the existing `AchievesGaussNorm` predicate,
  which is used directly.
- Project rg searches for `gaussNorm|GaussLeading|gaussLeading|convergentDivision`
  and the item id in `lean/WeilConjectures` and `lean/Sheaf`: only uses of
  Gauss norm in the presentation and affinoid modules; no division theorem.
  The exact item-id search gives no declaration. No duplicate is introduced.
- DAG search for leading exponents and `tools/blueprint_refs.py search
  'leading exponent'`: no separate definition node for this internal
  characterization. No new notion is introduced by a declaration.

Sources: the item explicitly labels its theorem an agent auxiliary result,
not a verbatim BGR theorem. I read the current blueprint unit
`literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/_section.md`
and the node's full seven-step proof. I also opened Bosch's April 2008 lectures
at https://www.uni-muenster.de/IVV5WS/WebHop/user/weckerm/heft378.pdf, the context
reference recorded in the node. The module docstring retains the agent
attribution and all seven proof steps, including the contraction sign,
coefficient continuity and support passage. There is no claim that the book
prints this general finite-list statement. No statement correction or
STATEMENT-DISPUTED issue was found.

Validation: every compile uses scompile.py with module mode and the delivered
public/proof import visibility. The first compile passed; a fresh compile was
started after correcting the sum parentheses during clause review. Final
preflight and delivery results are recorded below.

## Second reading by NE

Second reading performed by the maintainer's independent stage-2 reviewer on behalf of NE
(2026-10-24, delivery b731a5c2a8bd). The section first delivered under this heading was a
self-audit by the worker (it says so itself); it is kept below as "Worker self-audit".

Node statement, clause by clause, against `RestrictedSeries.exists_bounded_division`:

1. K a field complete for a real-valued nonarchimedean absolute value ->
   `(K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]`. NormedField
   gives a multiplicative real absolute value (trivial one allowed, as in the node);
   ultrametric + complete are exactly the node's hypotheses. Nothing stronger. OK.
2. s >= 0, t >= 0 -> `(s t : ℕ)`, no positivity. OK.
3. T_s = K<X_1..X_s> [def-trf-restricted-series-presentation] ->
   `MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin s ↦ 1)` (Mathlib
   Restricted.lean:33,107: coefficients ‖a_ν‖·1 → 0 along cofinite), the same object the
   dependency module uses. OK.
4. Gauss norm sup_ν |a_ν| -> `MvPowerSeries.gaussNorm norm (fun _ ↦ 1)` (GaussNorm.lean:57,
   ⨆ ν, ‖a_ν‖·∏1^ν); bounded for restricted series, so the real iSup is the true sup. OK.
5. Graded lex order and L(u) -> `toDegLex` (Mathlib DegLex: total degree first, then
   Finsupp lex with the first differing coordinate deciding). L(b_i) is rendered by the
   existential β with both clauses: `AchievesGaussNorm … (b i).val (β i)` (GaussNorm.lean:170,
   ‖coeff‖ = gaussNorm) and maximality in DegLex among achievers. This pins β i = L(b_i) by
   antisymmetry; existence follows from ‖b_i‖ = 1 and restrictedness (finitely many
   coefficients of modulus ≥ 1/2), so the ∃ adds no hypothesis and does not weaken. OK.
6. ‖b_i‖_G = 1 -> `hb`. No Gröbner hypothesis. OK.
7. f ∈ T_s, ∃ q_1..q_t, r ∈ T_s -> `f`, `∃ β q r` in the same subring. OK.
8. f = Σ q_i b_i + r -> `f = (∑ i : Fin t, q i * b i) + r` (parenthesised; without the
   parentheses r would fall under the binder). OK.
9. ‖q_i‖ ≤ ‖f‖ for every i, ‖r‖ ≤ ‖f‖ -> the two gaussNorm conjuncts. OK.
10. coefficient of X^ν in r nonzero ⇒ L(b_i) ≰ ν componentwise for every i ->
   `∀ ν, coeff ν r.val ≠ 0 → ∀ i, ¬ β i ≤ ν` with the plain Finsupp (pointwise) order. OK.
11. Empty list: t = 0 gives f = 0 + r, i.e. r = f, as a consequence. OK.

Edge cases: t = 0 (vacuous β/q, r = f forced); s = 0 (single exponent 0, T_0 = K, β i = 0,
any r must be 0, achieved by q_1 = f/b_1); f = 0; trivial absolute value (T_s = polynomials,
statement is polynomial division over K with unit-leading H_i = b_i); dense value groups.
Example b = X − a, |a| < 1, f = X: β = 1, q = 1, r = a satisfies every clause. The statement
is true by the node's seven-step proof (unit-modulus part H_i, MonomialOrder.div over
V = {|a| ≤ 1} per monomial, contraction ‖e_i‖ ≤ c < 1, geometric series), which I re-checked.

Records: node changed only in `lean` (diff against side-live); `lean.statement` is verbatim the
file signature; stmt_deps def-weil-field (Mathlib Field ⊂ NormedField) and
def-trf-restricted-series-presentation (public import of its module) are the only project
inputs; DegLex is publicly imported for `toDegLex`, Groebner is a plain proof-dep import.
One definition per notion: no declaration added; no `exists_bounded_division`, Tate division or
duplicate in side-live lean/Sheaf or lean/WeilConjectures; Mathlib has only MonomialOrder.div
(polynomial) and univariate formal Weierstrass division. No hollow definition, proof is `sorry`,
docstring carries source place, `(blueprint: lem-trf-tate-convergent-division)` and the
seven-step proof. Universe: only `u` for K, bound. No mismatch found; no Lean or node change.

### Worker self-audit (as first delivered)

The dispatch brief forbids starting another agent and specifies the maintainer's
independent review after delivery. This section records the worker's separate
clause review, not a claim that another worker independently reviewed it.
With the node and module open, I checked each binder, both orders, the
coefficient maximum, decomposition, both norm bounds, and the support exclusion
against the correspondence above. This review caught the sum-scope issue:
`∑ i, q i * b i + r` would put `r` inside the sum; it was changed to
`(∑ i, q i * b i) + r`. No node changes were required. I checked that the
existential `β` has an attaining clause as well as maximality, so it cannot
be an arbitrary exponent or a vacuous upper bound, and that no positivity
assumption excludes `s=0` or `t=0`. Independent mathematical acceptance remains
with the maintainer's delivery review.
