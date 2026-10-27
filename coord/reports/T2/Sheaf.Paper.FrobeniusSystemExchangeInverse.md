## What changed

Proved integral direct and compact exchange invertibility from their existing
whole-system invertibility and the existing `directAlpha_isIso` and
`compactAlpha_isIso` comparisons. Two proved private general-scheme helpers
upgrade the restricted alpha comparisons to natural isomorphisms, then use
preservation of isomorphisms under whiskering and composition for the specified
alpha/system/beta realization. The full constructible-subcategory inclusion
reflects the resulting component isomorphisms. The public proofs specialize
these arguments to the geometric Frobenius squares. The compact argument retains
the same chosen compactification in all factors.

No public signatures, definition bodies, imports, targets or unit routes change.
Local transparency attributes in the private-helper section keep the standard
derived-category localization folded. The arguments implement the original
integral-realization proof step, so no DAG route changes are needed.

## Proved and sorry left

Closed two of the six original holes:

- `WeilConjectures.FrobeniusExchange.frobeniusDirectIntegral_isIso`.
- `WeilConjectures.FrobeniusExchange.frobeniusCompactIntegral_isIso`.

Four original holes remain unchanged:

- `WeilConjectures.FrobeniusExchange.frobeniusSystemDirect_inverse_evaluation`.
- `WeilConjectures.FrobeniusExchange.frobeniusSystemCompact_inverse_evaluation`.
- `WeilConjectures.FrobeniusExchange.frobeniusDirectIntegral_inverse`.
- `WeilConjectures.FrobeniusExchange.frobeniusCompactIntegral_inverse`.

All belong to node `lem-weil-frobenius-system-exchange-inverse` and retain their
source and complete proof plans in their docstrings. No new holes, modules or
split-off statements. Both added private helpers are proved. Net two holes closed.
The full module compiled in 22.5 seconds through `lcompile.py`.

## No longer needed

None. No imports, nodes or dependency modules are removed. The finite-evaluation
and explicit inverse-formula assertions remain, so their dependencies are retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction. Componentwise expansion of realization factors caused
kernel timeouts through large derived-category conversions. Proving invertibility
of the natural transformations before taking components avoids that expansion.
The proofs use the actual fixed comparison maps and the full constructible domains
of the original statements, with no added hypotheses. Finite evaluation and the
explicit inverse-formula holes remain unchanged after exploratory attempts.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
