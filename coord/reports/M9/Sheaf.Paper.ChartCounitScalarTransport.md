## What changed

The pro-etale clause of `Sheaf.Paper.ChartCounitScalarTransport` is reduced to its
existing etale clause and the single-ring geometric counit evaluation identity.
The proof uses the actual `proEtaleCoefficientMap`, the supplied datum's
quasi-inverse and counit, and the displayed `geometricScalarIso`.
The coefficient/site diagram is proved by categorical cancellation; no coefficient
map is assumed invertible in that cancellation.

`Sheaf.Paper.ChartGeometricCounitEvaluation` isolates the single-ring evaluation
identity for arbitrary etale representatives and endpoint isomorphisms. Its
statement, complete proof outline, source and DAG node are included.

## Proved and sorry left

The pro-etale declaration
`AlgebraicGeometry.ProEtale.ChartFiniteRing.chartCounitScalarTransport`
is proved from its existing etale clause and the independent single-ring evaluation
identity. One of the two original theorem bodies is closed; one new hole is added.
This is a decomposition, with net hole reduction zero, rather than a proof without
new unfinished dependencies. There is no hole in a definition.

Every remaining hole, by declaration name:

- Retained original:
  `AlgebraicGeometry.ProEtale.ChartFiniteRing.chartCounitScalarTransport_etale`
  (node `lem-sp-chart-counit-scalar-transport`).
- New single-ring evaluation lemma:
  `AlgebraicGeometry.ProEtale.ChartFiniteRing.chartGeometricCounitEvaluation`
  (node `lem-sp-chart-geometric-counit-evaluation`).

The supplied proof of the pro-etale clause uses the actual coefficient map without
assuming its invertibility. The generic cancellation and endpoint transport helpers
were compiled separately. Both modules compiled together (45.5 s and 52.8 s). After removing the empty-line
style warning, a second complete compile passed with no warnings. The delivery
command performs its own validation. Four delivery attempts returned
`DELIVERY BUSY` before compiling or pushing.
The annihilator and all generic diagram helpers were independently compiled.

## No longer needed

No original public imports or declarations were removed. The generic site
conjugacy statement is not needed by the new
explicit proof of the pro-etale clause: it carries out their pointwise diagram
calculation directly. The etale clause remains unfinished and retains its original
raw-pasting and left-normalization dependencies. No module is withdrawn. In particular,
the quarantined item and its unfinished etale dependencies are preserved.

The unchanged original etale clause still needs
`lem-sp-raw-chart-scalar-counit-pasting`,
`lem-sp-chart-left-scalar-normalization`, and
`lem-sp-left-comparison-scalar-counit-pair`; these nodes are retained.

`lem-sp-site-scalar-counit-pair-conjugacy` is removed from this node's proof
dependencies: its role is performed by the explicit coefficient/site diagram.
The compatible left-comparison lemma remains needed by the retained etale proof
plan and refinement step, so it is not pruned.

## Where the brief, the DAG or earlier work was wrong

The DAG's declared dependency `Sheaf.Paper.ChartLeftScalarNormalization` is absent
from the current Lean tree and the quarantine tree searched for this item, despite
its Lean attachment. The unchanged etale clause requires the normalization bridge
recorded there. Its absence is not treated as a withdrawal.

The original etale and pro-etale declarations each contained one hole. Their
signatures and all existing non-theorem bodies are unchanged. The new single-ring
lemma is not a repackaging of either scalar theorem: it has one coefficient ring,
no ring map, no scalar-extension square, and no existential coefficient line.
The original theorem still requires the full scalar/site diagram calculation.
Edge checks: positivity of N is supplied by the datum, including N = 1 and the
zero ring; d = 0 uses the existing identity normalization, and empty schemes
require no nonemptiness. No flatness of the coefficient map is introduced.

The public ambient-adjunction counit theorem in
`EtaleProEtaleCoefficientCompatibility` cannot directly consume the restricted
adjunctions in `ChartFiniteRing.Datum`; the proof therefore uses its actual
coefficient/site square and a pointwise categorical calculation.

## New nodes

`lem-sp-chart-geometric-counit-evaluation`, module
`Sheaf.Paper.ChartGeometricCounitEvaluation`: a single-ring normalization result,
strictly part of the pro-etale scalar argument. It contains no coefficient change
and no existential root-line comparison.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
