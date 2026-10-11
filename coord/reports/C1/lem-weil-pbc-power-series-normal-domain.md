## Worker report

The module `lean/Sheaf/RingTheory/PowerSeriesNormalDomain.lean` states
`MvPowerSeries.noetherian_normal_domain`, with its only proof `sorry`. No definition,
instance, auxiliary theorem, new node, dependency replacement, or statement correction is needed.
Its docstring gives the five-step natural-language proof of the node with dependency identifiers.
The server single-file compile returned exit code 0 in 1.3 seconds, without warnings.

Each hypothesis and clause is rendered as follows:

- The arbitrary coefficient ring is `(R : Type u) [CommRing R]`, with `u` explicitly declared.
- Noetherianity of `R` is `[IsNoetherianRing R]`, exactly the dependency's recorded declaration.
- The normal-domain hypothesis is `[IsDomain R] [IsIntegrallyClosed R]`. The normal-ring
  dependency expressly identifies this conjunction as its domain clause. No local-normal-ring
  hypothesis is substituted for the domain clause.
- The one-variable ring is `MvPowerSeries (Fin 1) R`: exactly the power-series dependency's
  `MvPowerSeries (Fin n) R` specialized at `n = 1`. The exponent set `(Fin 1 →₀ ℕ)` has one
  natural exponent; the coefficient families and Cauchy product are precisely `R[[x]]`.
- The Noetherian conclusion is `IsNoetherianRing (MvPowerSeries (Fin 1) R)`.
- The integral-domain conclusion is `IsDomain (MvPowerSeries (Fin 1) R)`.
- Every fraction-field element satisfying a monic polynomial lies in the power-series ring:
  this is `IsIntegrallyClosed (MvPowerSeries (Fin 1) R)`. The definition uses `FractionRing`
  and `IsIntegralClosure`; `isIntegrallyClosed_iff` gives precisely
  `∀ {x : K}, IsIntegral A x → ∃ y, algebraMap A K y = x` for a fraction ring `K` of the
  domain `A`. `IsIntegral` means a root of a monic polynomial. The domain clause supplies
  nontriviality, so the fraction ring is a field.
- The three conclusions are joined by `∧`, with no extra clause and no extra hypothesis.

Dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`;
  its docstring and `isNoetherianRing_iff_ideal_fg` identify the finite-generation condition.
- `def-weil-pbc-normal-ring` (Mathlib leaf without a Lean record): its `mathlib_match` names
  `IsDomain`, `IsIntegrallyClosed`, and `Localization.AtPrime`. Read `IsDomain` in
  `Mathlib.Algebra.Ring.Defs`, `IsIntegrallyClosed` and its fraction-field characterization
  in `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, and `Localization.AtPrime` in
  `Mathlib.RingTheory.Localization.AtPrime.Basic`. This item uses only the domain clause,
  so the unused localization module is not imported.
- `def-weil-pbc-multivariate-power-series` (Mathlib leaf without a Lean record):
  `Mathlib.RingTheory.MvPowerSeries.Basic`, `MvPowerSeries`. Read the definition, module
  documentation, coefficient multiplication formula, and commutative-ring instance. Used
  directly at `Fin 1`; no private univariate definition or transport is introduced.

Edge cases checked before writing: the zero ring is correctly excluded by `IsDomain R`;
fields satisfy the hypotheses in every characteristic; the variable set has exactly one
member, as requested, and the theorem does not claim the empty-variable or arbitrary-variable
case. Zero fraction-field elements and zero coefficients satisfy integral closedness; the
proof docstring handles zero elements separately. There is no dimension, principal-ideal,
characteristic, completeness, or excellence assumption. Arbitrarily large coefficient-ring
universes are allowed by `universe u`.

Searches for an existing statement, all performed read-only:

- `msearch.py ... leanfinder` query: "power series ring over a Noetherian integrally closed
  domain is Noetherian and integrally closed". Eight hits: `PowerSeries.isNoetherianRing`,
  `PowerSeries.instIsNoetherianRing`, `PowerSeries.instIsDiscreteValuationRing`,
  the power-series UFD instance for a PID, `PowerSeries.instIsDomain`, and three unrelated
  function-field/Laurent-series results. No theorem for general Noetherian normal domains.
- `msearch.py ... loogle` query: `IsIntegrallyClosed, MvPowerSeries`. Zero hits.
- `msearch.py ... grep` query: `IsIntegrallyClosed|normal`, subdirectory
  `RingTheory/MvPowerSeries`. Zero hits.
- `msearch.py ... grep` query:
  `IsIntegrallyClosed.*(PowerSeries|MvPowerSeries)|(PowerSeries|MvPowerSeries).*IsIntegrallyClosed`.
  Zero hits.
- `msearch.py ... leansearch` query: "formal power series over a Noetherian normal domain
  are integrally closed". Service unavailable (Internal Server Error); no verdict assigned.
- `rg` in the source project's `WeilConjectures` for the item identifier: no hits.
- `rg` in the source project and `lean/Sheaf` for power-series normality/integral closedness:
  only unrelated power-series normalization results and other normal-ring statements;
  none states this result. Name search including `dag/lean_names_upstream.json` confirms
  the proposed `noetherian_normal_domain` name does not already occur.
- `rg` of Mathlib `RingTheory/PowerSeries` for `IsIntegrallyClosed|normal`: only normalization
  monoid results, no general integral-closedness result.

Source checked: local `literature/stacks-project/algebra.tex` is absent on this machine,
so read the primary source at https://stacks.math.columbia.edu/tag/0BI0, Lemma 10.37.9.
Its statement agrees exactly with the node. The proof agrees with the node's five-step
expansion. No statement dispute or node fault was found.

The independent second reading is left to the assigned second reader, as requested.

## Second reading by C1

I independently read the node statement, its Stacks source (Algebra, Tag 0BI0,
lines 8149–8174), the dependency records, and
`Sheaf/RingTheory/PowerSeriesNormalDomain.lean`. The introduced objects and their Lean
renderings are:

- The coefficient ring is `R : Type u` with `[CommRing R]`; the explicit universe permits
  every coefficient-ring universe covered by the node.
- Noetherianity is `[IsNoetherianRing R]`, the recorded Mathlib notion that every ideal is
  finitely generated.
- “Normal domain” is the conjunction of `[IsDomain R]` and
  `[IsIntegrallyClosed R]`. `IsIntegrallyClosed` is integrality in `FractionRing R`, so
  together these hypotheses exactly express the node's fraction-field monic-polynomial
  condition; no localization condition for a normal ring is accidentally assumed.
- The one-variable formal power-series ring is `MvPowerSeries (Fin 1) R`, the dependency
  notion specialized to one index. `Fin 1` has exactly one index, so this is the node's
  `R[[x]]`; no empty-variable or arbitrary-variable case is introduced.
- The conclusion is the conjunction
  `IsNoetherianRing (MvPowerSeries (Fin 1) R) ∧ IsDomain (MvPowerSeries (Fin 1) R) ∧
  IsIntegrallyClosed (MvPowerSeries (Fin 1) R)`. These are respectively the three clauses
  “Noetherian”, “integral domain”, and “every integral fraction-field element belongs to
  the ring”, in the same order and with no extra clause.

No mismatch was found and no source or Lean text was changed. The zero ring is excluded by
`IsDomain R`; fields in every characteristic satisfy the hypotheses; zero elements are
covered by `IsIntegrallyClosed`; and no characteristic, completeness, dimension, excellence,
or finiteness assumption is present. The `n = 0` power-series case is intentionally outside
the node because the source asks for one variable.

I searched Mathlib and the source project with LeanFinder/Loogle/LeanSearch-style queries and
`rg` for `MvPowerSeries`, `PowerSeries`, `normal`, and `IsIntegrallyClosed`. The only matches
were the component notions (`MvPowerSeries`, `IsNoetherianRing`, `IsDomain`, and
`IsIntegrallyClosed`) and unrelated power-series results; no existing theorem states the
Noetherian normal-domain result. The source repository has no declaration for this item. The
worker's recorded searches agree, including the unavailable LeanSearch attempt. Compilation
with `scompile.py` succeeds with only the permitted `sorry` warning.

## Reviewer fix (R-psd1314)

The node is the one-variable case, so R[[x]] is stated with Mathlib's one-variable
`PowerSeries R` instead of `MvPowerSeries (Fin 1) R` (lead's instruction: one variable uses
`PowerSeries`, as M1 82190d0f3 lem-weil-pbc-power-series-n2, which cites this node in its step 4
on `PowerSeries R`). The declaration is renamed to `PowerSeries.noetherian_normal_domain`; the
import is `Mathlib.RingTheory.PowerSeries.NoZeroDivisors` (its `IsDomain R⟦X⟧` instance
is all `IsIntegrallyClosed (PowerSeries R)` needs; no local instance is added).
Hypotheses (`CommRing`, `IsNoetherianRing`, `IsDomain`, `IsIntegrallyClosed`: STATE NORMAL RING
domain form) and the three conclusions are unchanged and match the node.
