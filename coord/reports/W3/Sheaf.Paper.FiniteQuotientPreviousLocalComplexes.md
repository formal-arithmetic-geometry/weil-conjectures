## What changed

Added a proof-only auxiliary module containing the single-chart conversion step and
used it to assemble the original theorem. The original theorem now pulls back the
previous-model sieve along every chart morphism and applies the auxiliary result.
The original public statement and imports are unchanged; the auxiliary import is
proof-only.

## Proved and sorry left

The original hole in `AlgebraicGeometry.Scheme.finiteQuotient_previous_local_complexes`
is closed by a compiling Lean proof. One strictly smaller obligation remains as the
whole theorem `AlgebraicGeometry.Scheme.finiteQuotient_previous_local_complexes_chart`
in `Sheaf.Paper.FiniteQuotientPreviousLocalComplexesAux`, with proof `:= by sorry`.
Holes closed: 1. Holes added: 1 (decomposition).

## No longer needed

The parent proof uses only `FinitePerfectModelsOn`, sieve pullback stability, and the
new chart theorem. The old direct proof dependencies on coefficient-layer tensor
calculations, successor cohomology, and general restriction machinery are no longer
direct dependencies of the parent node; they remain recorded on the chart node where
future work may use them. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The DAG's two-step plan bundled the local algebraic conversion and the sieve assembly.
The assembly is elementary once the chart conversion is named, but the conversion
requires a separate statement about transporting the canonical representative through
restriction and coefficient comparison. Splitting there gives a strictly smaller
obligation and preserves the exact original conclusion.

## New nodes

`lem-weil-pbc-finite-quotient-previous-local-complexes-chart` records the single-chart
conversion theorem and its source proof. Its Lean node and module are included in this
delivery.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteQuotientPreviousLocalComplexes": "ff1be87c0f42841e8915d66ad6cc79cb190cb6d4", "Sheaf.Paper.FiniteQuotientPreviousLocalComplexesAux": "0c24a83c78a6e2fabfaae17480b9376907d5aec0"}, "results": {}, "time": "2026-10-27T23:38:28+0800", "transitive": 0, "version": 1}
```

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
