## What changed

Retired Sheaf.AlgebraicGeometry.CartesianChartExchangeCoefficients in favor of
WeilConjectures.AlgebraicGeometry.CartesianChartExchangeCoefficients, following
the current retirement assignment. Its declaration bodies are identical to the
twin's after whitespace normalization. Changed only the private import in the
four direct consumers CartesianChartExchangeCore, CartesianChartExchangeSource,
CartesianChartExchangeAdjunction and CartesianChartExchangeTransport, plus
existing warning cleanup (line wrapping, heartbeat comments and placing the
private-module linter setting at module scope). The upstream source is untouched.

Change record: coord/changes/D2-cartesian-chart-exchange-coefficients-retirement.md.
Withdrawal: deleted.txt. No existing declaration signature or construction changes.

Validation: all four adapted consumers compile individually through lcompile.py.
The delivery dry run passes compilation, axiom probes and the server preflight
(review class CODEX). The import-graph check finds no remaining consumer of the
retired module and no twin pairs in any adapted consumer closure.

## Proved and sorry left

The assigned copy has zero original holes: proved 0 of 0; holes added 0; split off 0.
All seven private helpers already have complete proofs or constructions in the
upstream twin: comp_single, comp_single_inv, flatten, flatten_comp_left,
flatten_comp_right, raw_comp_named, raw_coefficient_square. No sorry remains in
any delivered module. The delivery is retirement progress, not a new proof.

## No longer needed

Pruned module Sheaf.AlgebraicGeometry.CartesianChartExchangeCoefficients.
Removed its `import all` from all four direct consumers and replaced each with
`import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeCoefficients`.
No DAG node or blueprint unit attaches to the retired module; no node is deleted,
no proof dependency is bypassed, and no other module is withdrawn. Searched current
and quarantined Lean and DAG sources for remaining references. Each migrated
consumer's closure contains no Sheaf/upstream twin pairs.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a module with holes or a repair. The current
queue and coord/retire-items.tsv identify this as a duplicate retirement with zero
holes. The older kept-twins record described twelve blocking copies, but all four
current consumer closures already use the upstream versions of those dependencies;
there is no remaining import collision. The copy and upstream twin have the same
seven private declarations. No mathematical statement or DAG correction is needed.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
