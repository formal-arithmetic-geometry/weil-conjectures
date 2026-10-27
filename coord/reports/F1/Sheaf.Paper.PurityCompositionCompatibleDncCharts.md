## What changed

Filled `WeilConjectures.PurityFiniteSetting.composition_compatible_tangent_normal`
in `Sheaf.Paper.PurityCompositionCompatibleDncCharts`, preserving its signature.
The private coordinate-evaluation proof identifies an affine etale chart with
an etale polynomial algebra, transports the polynomial differential basis by
Mathlib's formally etale differential comparison, and applies the universal
property of differentials to arbitrary modules. The composite chart is identified
with the base change of the second chart composed with the first by comparing
its two projections in the ordered-block Cartesian square. The tangent proof
then separates the ordered blocks and constructs extension and restriction of
derivations explicitly, with uniqueness from coordinate evaluation.

The existing imports already publicly expose the formally etale comparison,
polynomial differential basis and tensor-basis API; no extra import is needed.
Updated proof steps 2 and 4 of
`lem-pur-composition-compatible-dnc-charts` and recorded the two existing Mathlib
leaf dependencies. No definitions, public signatures, or target statements change.

The construction allows arbitrary commutative base rings, zero coordinate ranks,
and zero rings (empty affine schemes); no nonempty or positive-rank case split
is used. The unit's orientation and tensor-composition route is retained.

Validation: the complete module after import cleanup compiled on the project
server in 23.0 seconds. Its axiom print lists only `propext`, `Classical.choice`,
and `Quot.sound` for the newly proved theorem.

## Proved and sorry left

Closed 1 of the module's 2 original holes:
`WeilConjectures.PurityFiniteSetting.composition_compatible_tangent_normal`
(node `lem-pur-composition-compatible-dnc-charts`). The two new private helpers
`coordinateDerivation_bijective` and `compatibleCompositeChart_etale` are proved.

One original hole remains, unchanged:
`WeilConjectures.PurityFiniteSetting.compatibleNu_etale_restriction`
(node `lem-pur-composition-compatible-dnc-charts`). No holes were added, and no
statements were split off. The final DNC assembly and the other existing proofs
are retained.

## No longer needed

Removed the provisional imports `Mathlib.RingTheory.Etale.Kaehler`,
`Mathlib.RingTheory.Kaehler.Polynomial`, and
`Mathlib.LinearAlgebra.TensorProduct.Basis` because the original imports
already expose their APIs. The final import list is identical to the
original. No nodes or modules withdrawn. The tangent calculation
uses Mathlib directly instead of extracting a differential frame from the DNC
normalization theorem. That normalization dependency remains needed by the actual
normal-cone splitting and final DNC assembly. All other declared dependencies are
retained for those proofs and the original restriction obligation.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was found. The previous proof plan's
coordinate-frame step admits the direct Mathlib proof recorded above. The
remaining restriction obligation concerns compatibility of the specified
zero-section base-change and monoidal site-comparison constraints; searches did
not locate an existing theorem with that exact equation. This is a partial proof
delivery, with its original restriction theorem left available as the next item.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
