## What changed

Proved `AlgebraicGeometry.exists_completed_chart_of_logRegular` with its exact existing
signature. The existing, more general
`AlgebraicGeometry.exists_completed_chart_of_logRegularAt` supplies the pointwise
chart and completion presentations. The new proof establishes its regular-local
hypothesis, transports maximal-ideal completions and residue fields through the
canonical strict-local-ring comparison, and proves the missing characteristic-zero
conclusion by domain descent and the finite prime-field contradiction.

Two proved private helpers transport a completed model along a coefficient-field
isomorphism, preserving every monomial, and show that a domain containing no field
has characteristic zero. No choices of arbitrary data from new unproved existence
statements and no new public definitions are introduced.

Removed `CompleteToricModel`'s unused public import of this theorem module, preserving
its public prerequisite imports explicitly, so the existing pointwise theorem can
be imported without a cycle. Every `ToricMonoid` declaration is unchanged. This
interface change and all downstream users are documented in
`coord/changes/H1-completed-chart-model-import-cycle.md`.

Validation: the item, the changed model and all 16 original direct importers compile
cleanly via `lcompile.py --all`; per-file times range from 1.3 to 13.3 seconds
(the item: 11.8 seconds). Every temporary importer source copy was removed.

Updated the item's DAG proof and proof dependencies to match this route. The unit's
statement and steps are unchanged; this auxiliary node realizes no unit step.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.exists_completed_chart_of_logRegular`
(node `lem-trf-log-regular-completed-chart`). Zero holes remain in the item.
Zero holes added; zero statements split off. Both private helpers are completely
proved. The existing imported pointwise and saturated-model normality theorems
remain separate stated dependencies; this delivery does not claim to prove them.

## No longer needed

Removed these direct private imports from the item:

- `Sheaf.RingTheory.FormalMonoidRingDimension`
- `WeilConjectures.RingTheory.StrictHenselizationNoetherian`
- `WeilConjectures.RingTheory.CompletionDimension`
- `WeilConjectures.RingTheory.CohenPowerSeriesPresentation`
- `WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete`
- `WeilConjectures.RingTheory.AdicCompletionNoetherian`
- `Mathlib.RingTheory.AdicCompletion.Functoriality`
- `Mathlib.RingTheory.AdicCompletion.Completeness`
- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`
- `WeilConjectures.RingTheory.CohenRing`

The main proof no longer directly needs the old proof nodes
`lem-trf-log-regular-sharp-chart`, `lem-sc-strict-henselization-noetherian`,
`lem-trf-completed-chart-coefficient-surjection`,
`lem-trf-polynomial-power-series-monoid-completion`,
`lem-weil-pbc-power-series-field-cohen-regular-complete`,
`lem-trf-formal-monoid-ring-dimension`, `def-weil-pbc-krull-dimension-ring`, and
`lem-trf-cohen-monoid-surjection-principal-kernel`: these constructions are already
packaged by the existing pointwise result. Most are still needed by its own proof
plan, so no global withdrawal is requested. No module or declaration is deleted.
No top-level `tool_uses` approval is removed.

Also removed the unused upward import
`Sheaf.AlgebraicGeometry.LogRegularCompletedChart` from `CompleteToricModel`.
The entire original public interface of the item itself stays unchanged.

## Where the brief, the DAG or earlier work was wrong

The stated ring-theoretic proof inputs were already available, but all model-based
ones had an accidental import path back to the item through `CompleteToricModel`.
That import used none of this item's declarations; removing it repairs the cycle
rather than introducing duplicate ring constructions.

The library already states the completed-chart result under pointwise hypotheses
in `PointwiseLogRegularCompletion`; rebuilding its coefficient and dimension
argument here would duplicate existing work. Its conclusion omits characteristic
zero in the no-field case; this delivery supplies that additional conclusion from
normality and faithful flatness. Trivial monoids and zero parameters require no
special case in any of the transport arguments.

Searches: LeanFinder for same-dimension surjective ring maps found the Mathlib
nonzero-divisor dimension inequality; Loogle for `ringKrullDim, RingHom.ker` had
no exact match. Grep confirmed the existing pointwise theorem and the model import
cycle. LeanFinder also searched residue-field transport; the proof uses Mathlib's
`IsLocalRing.ResidueField.mapEquiv` directly.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
