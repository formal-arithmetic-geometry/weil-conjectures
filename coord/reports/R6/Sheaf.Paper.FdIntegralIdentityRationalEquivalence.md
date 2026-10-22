## What changed

Proved `WeilConjectures.fdIntegralIdentityRationalEquivalence` with its statement unchanged.
The integral equivalence is the existing completed-coefficient presentation equivalence,
restricted using the integral constructibility characterization. Exactness and all integer
shift pins descend through the fully faithful inclusions. Projection normalization identifies
constant scalar sections; descent from complexes proves integral semilinearity, and full
faithfulness proves it for the inverse. Raw semilinear localization gives inverse rational
functors, their tensor and scalar formulas, and exactness by the integral-image triangle
criterion. The original coefficient-presentation theorem supplies the prescribed finite
reductions and their unit equation. The packet contains the assigned Lean module, its proof
node, and the required interface-command record is `coord/changes/fd-integral-identity-proof-interface.md`; it documents the private
instances and local elaboration settings, with zero downstream consumers to adapt.

## Proved and sorry left

Closed the one original hole: `WeilConjectures.fdIntegralIdentityRationalEquivalence`.
Added no holes and split off no statements. No `sorry` remains in the delivered module.
Existing named dependencies retain their own independently assigned proof obligations.

## No longer needed

No planned node or module is withdrawn. The proof uses the existing four-step route,
with proved library constructions replacing its elementary constructions. No dependency
can be pruned from an unfinished parent merely because it has no current Lean importer.
Removed redundant private imports `Sheaf.Paper.SfIntegralConstructibleTriangulated`,
`Sheaf.CategoryTheory.ScalarLocalizationTriangulated`, and
`Sheaf.CategoryTheory.ScalarLocalization`; their APIs remain available through the
proof imports that use them. All additional imports are private proof imports.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was required. Preflight requested an interface-command
change record for the private instances and local attributes; the record is included.
The DAG's original plan omitted the already available completed-coefficient equivalence and generic semilinear localization
API; the proof dependencies and step descriptions now explicitly record their use.
The independent universes, raw categories (without adjoining retracts), canonical
coefficient maps, and normalized finite reductions are preserved.

## Second reading by R6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
