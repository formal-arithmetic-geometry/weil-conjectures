## What changed

Retired the zero-hole duplicate `lean/Sheaf/AlgebraicGeometry/CartesianChartExchangeComparison.lean`
and listed it in `deleted.txt`. Its private `chartRawAdj_pullback` theorem is already present with
a complete proof in `WeilConjectures.AlgebraicGeometry.CartesianChartExchangeComparison`.
Migrated the three direct consumers (`CartesianChartLiftRawNaturality`, `CartesianChartLiftNaturality`,
and `CartesianChartLiftCoherence`) from the duplicate proof import to the adopted source twin. Public
imports, declarations, signatures and mathematical statements are unchanged.
The record is `coord/changes/B9-cartesian-chart-exchange-comparison-retirement.md`.
The two previously unformatted consumer files are wrapped to at most 100 characters per line;
local proposition-valued `letI` bindings in proof bodies use `let`, the unused `hr` hypothesis is
explicitly referenced, and an unused simp argument is removed. No linter is disabled.

Validation: all three migrated consumers compile without warnings using `lcompile.py`
(Coherence 33.4 seconds, RawNaturality 53.4 seconds, Naturality 48.6 seconds).
All public imports and normalized declaration signatures are unchanged; no `sorry` is added.

## Proved and sorry left

This retirement starts with zero `sorry`s and leaves zero `sorry`s. No declaration is added and no
hole is split off. The upstream twin retains the complete proof of `chartRawAdj_pullback`.

## No longer needed

The duplicate module `lean/Sheaf/AlgebraicGeometry/CartesianChartExchangeComparison.lean` is
withdrawn. The three `import all Sheaf.AlgebraicGeometry.CartesianChartExchangeComparison` proof-only
imports are no longer needed and are replaced by the corresponding `WeilConjectures` import. No DAG
node or unit dependency is removed; the upstream declaration remains the canonical implementation.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an open theorem, but the current retirement table explicitly
lists this item as a zero-hole duplicate retirement. The source module and its private theorem are
complete, so proving a second copy would violate the one-definition-per-notion rule. No mathematical
statement correction is needed. The single theorem and its complete proof are byte-identical
to the upstream theorem. No DAG node, unit record or quarantined module refers to the duplicate
implementation; the raw-adjunction node already points at the upstream Conclusion module.
All three consumer import closures lose the Comparison twin pair and contain no twin pairs
after migration. `tools/downstream.py` confirms these are all three transitive users.

## Forced adaptations

The three consumer modules are unclaimed and are adapted only because their original
proof-only import names the withdrawn duplicate. The required import change replaces the withdrawn import with
`import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeComparison`; no theorem,
definition, signature, visibility, or mathematical argument changes. The warning cleanup recorded above is mechanical. The original modules compile against
the baseline because the duplicate is present; after withdrawal the unchanged import fails with
an unavailable module, so these import migrations are required. The migrated consumer modules
compile against the delivered upstream dependency.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
