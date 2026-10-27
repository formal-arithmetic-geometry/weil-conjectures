## Worker report

The module `Sheaf.RingTheory.TateIntegrallyClosed` states
`RestrictedSeries.tate_isDomain_and_isIntegrallyClosed`, with one postponed theorem
and no new definition. The node is unchanged except for its `lean` record.

Hypothesis and clause correspondence:

- The field K is `(K : Type u) [NontriviallyNormedField K]`, with the universe
  explicitly declared. This class extends `NormedField`, hence Mathlib `Field`
  from `def-weil-field`. Its norm is real-valued and multiplicative, and its
  `non_trivial` field asserts `∃ x, 1 < ‖x‖`. For a field this is equivalent to a
  nontrivial absolute value: a nonzero value below one has inverse above one.
- Nonarchimedeanness is `[IsUltrametricDist K]`. Since the metric of a normed field
  is induced by its norm, this is exactly the ultrametric triangle inequality.
- Completeness for that absolute value is `[CompleteSpace K]`; no alternative
  topology or discrete-value hypothesis is introduced.
- The nonnegative integer d is `(d : ℕ)`, without a positivity assumption.
- T is precisely `MvPowerSeries.IsRestricted.subring (R := K)
  (fun _ : Fin d ↦ (1 : ℝ))`, the subring used by the recorded dependency
  `Sheaf.RingTheory.RestrictedSeriesPresentation`. Reading Mathlib's
  `MvPowerSeries.IsRestricted` shows that it requires the weighted coefficients
  to tend to zero along the cofinite filter. At radius one the weight is one.
  Ring operations are inherited from formal multivariate power series, hence
  coefficientwise addition and the finite Cauchy product. There is no replacement
  completion, arbitrary ring, or extra presentation hypothesis.
- The first conjunct `IsDomain T` asserts nontriviality and no zero divisors.
- The second conjunct `IsIntegrallyClosed T` abbreviates
  `IsIntegralClosure T T (FractionRing T)`. In the presence of the first conjunct,
  `isIntegrallyClosed_iff (FractionRing T)` identifies it with
  `∀ {z : FractionRing T}, IsIntegral T z → ∃ t, algebraMap T (FractionRing T) t = z`.
  `IsIntegral` means a monic polynomial vanishes at z, so this renders exactly the
  node's fraction-field clause, without assuming integral closure as a hypothesis.
- The zero-variable case is included by `Fin 0`: it has one monomial exponent
  (the empty exponent), so every coefficient family is constant and restricted.
  Thus this is the constant field case of the same subring, without a separate
  noncanonical identification or an excluded edge case.

Declarations and imports inspected:

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs`, read with
  the full `NormedField` and `NontriviallyNormedField` signatures in
  `Mathlib.Analysis.Normed.Field.Basic`.
- `def-trf-restricted-series-presentation`: the recorded module
  `Sheaf.RingTheory.RestrictedSeriesPresentation` was read in full, including
  `RestrictedSeries.constants`, `IsTopologicallyFinitelyPresented`,
  `IsAffinoidQuotient`, and `HasBoundedTopologicallyGeneratedImage`. It already
  uses Mathlib's restricted subring. The latter three predicates concern the
  dependency's other clauses and are not assumptions of this theorem. The exact
  subring and its docstring were read in `Mathlib.RingTheory.MvPowerSeries.Restricted`.
- `def-weil-pbc-normal-ring`: its recorded
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed` is a public import, giving
  `IsIntegrallyClosed`; its documented normal-domain conjunction is used directly.
- Proof-only imports: `Mathlib.RingTheory.Ideal.Quotient.Operations` for
  `def-weil-pbc-algebra-hom-quotient` (`Ideal.Quotient.mkₐ` and quotient algebra),
  and `Mathlib.RingTheory.AdjoinRoot` for `lem-weil-pbc-monic-quotient-free`
  (`AdjoinRoot.powerBasis'`, whose full signature and docstring were read).
  The source proof dependency `def-trf-restricted-series-presentation` is already
  imported publicly. The remaining proof dependencies currently have no Lean
  record or Mathlib match: gauss-completion, tate-gauss-multiplicative,
  triangular-distinguished-coordinate, tate-weierstrass-norm-division, and
  normal-domain-monic-prime-factorization. They are identified by their exact
  node ids in the theorem's seven-step proof docstring; no replacement claims
  or invented declarations are assumed here.

Edge cases checked before writing: d = 0 as above; arbitrary characteristic;
non-discrete real value groups; zero integral element; elements already in T;
monic degree zero (the constant polynomial 1 has no root in a nonzero fraction
field); units and empty prime factor lists in the proof plan. The field excludes
the zero ring. No positive-dimension, separability, Noetherian, or discretely
valued hypothesis is present. The two conclusion predicates require no missing
Gauss-norm instance on the series ring: they are algebraic predicates on the
actual subring. There are no node faults, disputed statements, new nodes,
dependency repairs, or statement corrections.

Searches (2026-10-24), using `msearch.py Q32 lem-trf-tate-integrally-closed`:

- LeanFinder: `Finite variable Tate algebras over complete nonarchimedean fields
  are integrally closed domains`: eight hits on function-field integral closures
  and Laurent-series completions, none on the restricted subring.
- Loogle: `MvPowerSeries.IsRestricted, IsIntegrallyClosed`: zero hits.
- Mathlib grep: `IsIntegrallyClosed|UniqueFactorizationMonoid|IsDomain` in
  `RingTheory/MvPowerSeries`: zero hits. The restricted subring construction
  was then read directly rather than duplicated.
- LeanSearch: `A Tate algebra of restricted power series over a complete
  nonarchimedean field is an integrally closed domain`: eight hits on generic
  integral closures, valuation rings, and formal power-series domains, none an
  integral-closure theorem for Tate algebras.
- Project `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, and the upstream
  name index: Tate/restricted with integrally closed, factoriality, and normal
  domain phrases; no matching statement. The exact blueprint id search in
  `lean/WeilConjectures` also gave no match. The proposed declaration name has
  no previous occurrence. Broader regex hits were unrelated normalization or
  factorization results, inspected and discarded.

Source check: read Kedlaya's PDF online, its definition on p. 1, Theorem 3 on
pp. 3–4, and Proposition 5 on p. 5. The definition agrees with the restricted
subring, and Proposition 5 gives factoriality, from which the node asks only
normality. Source: [Kedlaya, Tate algebras](https://kskedlaya.org/18.727/tate-algebras.pdf).
The current blueprint ancestor's proof was read from `literature/blueprint/latest/`;
this is the historical analytic prerequisite recorded in the node, and neither
the unit statement nor its contracting-correspondence route is changed.
The full seven-step accepted node proof, including the monic-quotient comparison
and finite denominator cancellation, is transcribed in the theorem docstring.

Validation: the prescribed `scompile.py` compiled the module in sandbox and library
contexts without errors or additional warnings. Both implicit-variable options
are disabled, the universe is explicit, and every line is within 100 characters.
The only postponed proof is the named theorem recorded in the node.

## Second reading by Q32

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
