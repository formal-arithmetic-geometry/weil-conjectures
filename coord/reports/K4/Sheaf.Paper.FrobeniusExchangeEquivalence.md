## What changed

Proved `WeilConjectures.FrobeniusExchange.compactSupportFrobeniusExchange_isIso`
by specializing the existing
`WeilConjectures.PodConstructibleMate.frobenius_exchanges_isIso` to
`AlgebraicClosure (Padic l)` and taking its rational conjunct. That theorem
uses precisely the same canonical `frobeniusRational` and
`frobeniusCompactModel`; its model-scheme hypotheses are weaker. The auxiliary
algebraic closure is used only to instantiate the theorem's common-stage clause.
Added its module as a private proof import and removed the former private proof
imports. All existing declaration signatures and public imports are preserved.
Updated the assigned node's proof, proof dependencies and proof origin to match.

The import-direction check accepted the new dependency. A traversal of statement
and proof dependencies (including proof-step uses) found no path from
`lem-pod-constructible-mate-coherence` back to the assigned node. The unit's
statement and assembly steps remain in place: this is reuse of an already stated
Frobenius exchange result below the unit level. The existing theorem remains an
open proof dependency; this delivery does not claim its proof is complete.

## Proved and sorry left

Closed 1 of 1 holes:
`WeilConjectures.FrobeniusExchange.compactSupportFrobeniusExchange_isIso`
(node `lem-coef-frobenius-exchange-equivalence`).
No holes remain in the delivered module. No new holes, modules or statements
were added, and no holes were split off.

The reused declaration
`WeilConjectures.PodConstructibleMate.frobenius_exchanges_isIso`
(node `lem-pod-constructible-mate-coherence`) already has `sorry` in the library;
it is unchanged. This is a complete proof from an existing stated dependency,
not a claim that the targets' transitive axiom audit is now closed.

Validation: the final single-file remote compile passed in 3.8 seconds with no
diagnostics, after removal of the redundant private Mathlib import. The delivery
tool records its own compile, axiom probe and preflight. Two delivery attempts
returned exit 75 (all six priority slots busy) before running their checks;
neither was a Lean or packet failure.

## No longer needed

Removed these private proof imports from the assigned module:

- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.Paper.QcqsCompactSupportRealization`
- `Sheaf.Paper.IsomorphismDerivedPullback`
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`
- `Sheaf.Paper.SfRationalizationKaroubi`
- `Sheaf.Paper.SfIntegralCompactSupportConstructible`
- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.Paper.FiniteCoefficientAdjointComparisons`

The original direct proof-dependency edges are no longer used by this proof:

- `def-weil-weil-sheaf-complex`
- `def-weil-proetale-inverse-image`
- `def-weil-integral-rational-qbar-compact-support`
- `lem-weil-isomorphism-derived-pullback`
- `lem-weil-proetale-isomorphism-inverse-image`
- `def-pur-integral-derived-operations`
- `def-weil-rationalization-karoubi`
- `def-weil-derived-pullback-tensor-hom`
- `lem-sf-integral-compact-support-constructible`
- `lem-sf-proetale-constructible-origin`
- `lem-weil-pbc-normalized-etale-origin-witnesses`
- `fix-lem-exchanges`

These prerequisites may still be reached transitively or used by other results;
no global unreachability or module withdrawal is claimed. The six former
`tool_uses` approvals were removed from this node because its proof now uses the
existing stronger theorem instead. The retained public imports continue to
provide the existing public statement interface.

## Where the brief, the DAG or earlier work was wrong

The earlier duplicate search missed the rational conjunct of
`PodConstructibleMate.frobenius_exchanges_isIso`, now present in
`Sheaf.Paper.ConstructibleMateCoherence`. It proves exactly the required map
invertible and also handles nonseparated models and common coefficients. Thus
reimplementing the seven-step inverse-square plan is unnecessary for this item.
The old theorem docstring still records that valid mathematical plan; the node
and the actual Lean proof record the shorter reuse route.

The current source exists despite the historical quarantine entry in
`coord/rework.tsv`; it was copied intact before replacing its proof. No archived
module or dependency was withdrawn.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
