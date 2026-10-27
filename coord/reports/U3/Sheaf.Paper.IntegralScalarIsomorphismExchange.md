## What changed

In `Sheaf.Paper.IntegralScalarIsomorphismExchange`, proved `finiteCoherent`
using the existing `proEtaleCoefficientInverseImageMap_comp` theorem, via a
proof-only import of `Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition`.
The proof supplies the existing finiteness instance for the positive coefficient
quotient, applies `Iso.ext`, and uses canonical constant-ring composition.
No declaration signature or definition changed.

## Proved and sorry left

Closed `WeilConjectures.IntegralScalarExchange.finiteCoherent` (1 hole).
No holes added and no split-off statements.

The following seven existing holes remain, all attached to
`lem-pur-integral-scalar-isomorphism-exchange`:

- `WeilConjectures.IntegralScalarExchange.openInverse_isIso`
- `WeilConjectures.IntegralScalarExchange.integralScalarIsomorphismExchange_integral`
- `WeilConjectures.IntegralScalarExchange.integralScalarIsomorphismExchange`
- `WeilConjectures.IntegralScalarExchange.rectangle_naturality`
- `WeilConjectures.IntegralScalarExchange.scalarPull_finiteTor`
- `WeilConjectures.IntegralScalarExchange.rectangle_refinement`
- `WeilConjectures.IntegralScalarExchange.Systems.strictScalarIsomorphismExchange`

## No longer needed

None. All existing imports and planned dependencies remain needed for the
unfinished main argument. The coherence helper uses the existing constant-ring
composition node; no new node is introduced.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The existing constant-ring composition theorem
already supplies the finite coherence helper directly. Local derived-category
instance priorities and irreducibility attributes prevent expensive elaboration
of the existing completed coefficient constructions; these are local only.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
