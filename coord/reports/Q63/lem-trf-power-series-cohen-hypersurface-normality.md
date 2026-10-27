## Worker report

The module `Sheaf.RingTheory.PowerSeriesCohenHypersurfaceNormality` states
`MvPowerSeries.power_series_cohen_hypersurface_normality`, with one `sorry` and
no new definitions. The node copy changes only `lean`; no dependency repair,
new node, statement correction, or disputed statement is needed.

The conjunction packages the two cases of the node, for each natural number `d`.
All variables and both universes are explicitly bound, with `autoImplicit false`.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Integer `d ≥ 0`, including zero | `(d : ℕ)`; no positivity hypothesis |
| Case (i), any field `k` | `∀ (k : Type u) [Field k]` |
| `S = k[[X_1,…,X_d]]` | `MvPowerSeries (Fin d) k` |
| Case (ii), a commutative Cohen ring with prime uniformizer `p` | `∀ (C : Type v) [CommRing C] (p : ℕ), IsCohenRing p C →`; the recorded predicate includes `Nat.Prime p`, domain, DVR, maximal ideal equal to `Ideal.span {(p : C)}`, and completeness |
| `A = C[[X_1,…,X_d]]` | `MvPowerSeries (Fin d) C` |
| Arbitrary equation with constant coefficient exactly `p` | `∀ (Θ : MvPowerSeries (Fin d) C), constantCoeff Θ = (p : C) →` |
| `n = (p, X_1,…,X_d)A` | `Ideal.span (insert (MvPowerSeries.C (p : C)) (Set.range (X : Fin d → MvPowerSeries (Fin d) C)))` |
| `Θ ∈ n \ n²` | Consecutive membership and nonmembership conjuncts for that ideal and its square |
| `S = A/(Θ)` | `MvPowerSeries (Fin d) C ⧸ Ideal.span {Θ}` |
| Both rings regular local | `IsRegularLocalRing` on the respective explicit rings; this class includes localness and Noetherianity |
| Both rings nonzero integral domains | `IsDomain` on the respective explicit rings; this class extends `Nontrivial` |
| Both rings integrally closed in their fraction fields | `IsIntegrallyClosed` on the respective rings, using Mathlib's `FractionRing` definition |
| No perfectness of `C/pC` | There is no perfectness, Frobenius, or residue-field hypothesis |
| `d = 0` gives `S = k` | `d = 0 → Nonempty (MvPowerSeries (Fin d) k ≃+* k)` |
| `d = 0` gives `S = C/pC` | `d = 0 → Nonempty ((MvPowerSeries (Fin d) C ⧸ Ideal.span {Θ}) ≃+* (C ⧸ Ideal.span {(p : C)}))` |

The zero-variable equalities of mathematical rings are expressed as ring
isomorphisms, since function-valued power series and ideal quotients are not
definitionally their coefficient rings. `Nonempty` here expresses the asserted
isomorphism in a proposition; it is not used to manufacture definition data.

Statement dependencies read and reused:

- `def-weil-pbc-multivariate-power-series`: `MvPowerSeries` from
  `Mathlib.RingTheory.MvPowerSeries.Basic`, including `C`, `X`, and `constantCoeff`.
- `def-weil-pbc-cohen-ring`: `IsCohenRing` from
  `WeilConjectures.RingTheory.CohenRing`; its full conjunction was read.
- `def-weil-regular-scheme`: its recorded `mathlib_match` supplies the ring clause,
  `IsRegularLocalRing` from `Mathlib.RingTheory.RegularLocalRing.Defs`.
  The primary record `AlgebraicGeometry.IsRegularScheme` was also read, but the
  scheme clause is not needed for this ring theorem. No redundant scheme import
  or duplicate definition is introduced.
- `def-weil-pbc-normal-ring`: `IsDomain` and `IsIntegrallyClosed`, using the
  recorded inline normal-domain convention. The latter is imported from
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`.

All stated proof dependencies are imported privately, and their declarations
and proof docstrings were read:

- `WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete`:
  `MvPowerSeries.power_series_field_cohen_regular_complete`.
- `WeilConjectures.RingTheory.PowerSeriesQuotientVariables`:
  `MvPowerSeries.quotient_first_variables`.
- `WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`:
  `IsRegularLocalRing.quotient_span_singleton`.
- `WeilConjectures.RingTheory.RegularLocalLocalization`:
  `IsRegularLocalRing.localization_at_prime_and_isRegularRing`.
- `WeilConjectures.RingTheory.RegularRingNormal`:
  `IsRegularRing.isNormalRing`.

The remaining proof dependencies are the same Cohen, power-series, and normality
definition nodes already used publicly. The private import
`Mathlib.RingTheory.MvPowerSeries.Equiv` provides `MvPowerSeries.isEmptyEquiv`
for the zero-variable proof. The declaration docstring records all five proof
steps, including domain cancellation for `p ∉ p²C` and the explicit inverse of
localization at a local ring's maximal ideal.

Sources checked locally: `literature/stacks-project/algebra.tex`, labels
`remark-Noetherian-complete-local-ring-universally-catenary` (032C),
`definition-cohen-ring` (0327), `lemma-regular-ring-CM` (00NQ),
`lemma-localization-of-regular-local-is-regular` (0AFS), and
`lemma-regular-normal` (0567). The constant-coefficient argument remains
identified as agent-origin, as in the node, rather than attributed verbatim
to a Stacks theorem.

Edge cases checked before drafting:

- With `d = 0`, `Fin 0` is empty and `MvPowerSeries.isEmptyEquiv` is constant
  coefficient with inverse `C`. Thus the equation becomes `p`, the ideal `n`
  becomes `(p)`, and the Cohen quotient becomes `C/(p)`.
- The Cohen uniformizer is nonzero and nonunit, since the ring is a domain
  and its nonzero proper maximal ideal is `(p)`. Thus the cancellation argument
  excluding `p ∈ p²C` remains valid also for `d = 0`.
- With at least one variable, `Θ = p + X_1` satisfies the hypotheses and is
  outside `n²`; `Θ = p` also satisfies them. No nonconstant-term condition appears.
- Constant coefficient `p²` is excluded intentionally: for `Θ = p²` the quotient
  has a nonzero nilpotent image of `p`, so the asserted normal-domain conclusion
  would fail. The equality with `p` was not relaxed to divisibility by `p`.
- Arbitrary field characteristics and imperfect Cohen residue fields are included.
  The two cases use independent explicit universes `u` and `v`.

Searches actually run using `msearch.py`, group Q63 and this item:

1. LeanFinder query: "A multivariate formal power series ring over a field is
   regular local and a normal domain; over a Cohen ring a series with constant
   coefficient p defines a regular local normal hypersurface." Eight hits:
   univariate DVR/UFD/Weierstrass results and `MvPowerSeries.instIsLocalRing`;
   no exact theorem for this statement.
2. Loogle query: `MvPowerSeries, IsRegularLocalRing`. Zero hits.
3. Grep query: `IsRegularLocalRing|IsIntegrallyClosed|hypersurface`, scoped to
   `RingTheory/MvPowerSeries`. Zero hits.
4. LeanSearch query: "Multivariate formal power series over a field and Cohen
   power series hypersurfaces with constant coefficient p are regular local
   normal domains." Eight hits including `MvPowerSeries`, `constantCoeff`,
   `mem_nonZeroDivisors_of_constantCoeff`, and `isUnit_iff_constantCoeff`, with
   univariate local/Noetherian facts; no exact theorem.
5. Direct `rg` searches of both `lean/WeilConjectures` and `lean/Sheaf` for
   hypersurfaces and power-series/Cohen normality, and the item-id search in
   `lean/WeilConjectures`, found only other hypersurface statements and a
   proof-docstring use of this item in `SupportedCoordinateCoverUnitsPrimes`.
   The latter assumes the normality conclusion in its proof and does not state
   the present theorem. Exact searches for the proposed declaration/module name
   in those trees and `dag/lean_names_upstream.json` found no existing declaration.

Validation: `scompile.py` compiled the sandbox module and its library-module
identity cleanly (16.9 s and 5.3 s reported). There are no diagnostic commands,
implicit binders, local notation, auxiliary axioms, or definition data postponed
with `sorry`. The sole theorem proof is `sorry`, as required for stage 2.

## Second reading by Q63

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
