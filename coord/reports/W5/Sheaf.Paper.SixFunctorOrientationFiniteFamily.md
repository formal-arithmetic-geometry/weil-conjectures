## What changed

Proved `WeilConjectures.sfOrientationPrimeUnit` in
`Sheaf.Paper.SixFunctorOrientationFiniteFamily`. Map the proved base-field unit
`dlAdicBasePrimeUnit D C` along `algebraMap D.k₀ D.k`, then along the composite
of `Scheme.ΓSpecIso` inverse and the structure morphism on global sections.
`map_natCast` identifies the resulting image with the coefficient prime.
The proof uses declarations already exposed by the existing imports. All signatures,
definitions, public imports, and orientation comparison equations are unchanged.
The argument applies also to the empty scheme, since ring homomorphisms preserve units.

Validation: remote single-file compilation through `lcompile.py`; delivery preflight
provides the independent signature and axiom checks.

## Proved and sorry left

Closed the sole original hole: `WeilConjectures.sfOrientationPrimeUnit`
(node `def-sf-orientation-finite-realization`). Proved 1 of 1 original sorries.
No holes remain in the item. No holes added and no statements split off.

## No longer needed

None. Both original public imports supply declarations used in the existing
statements and definitions. No nodes or modules are withdrawn. The node's
proof list was empty; the proof implements the existing theorem docstring's
unit-transport argument without changing the orientation construction or unit route.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was required. The item is a definition module with
one auxiliary theorem hole, so its existing DAG node has no numbered proof plan.
The required field-unit fact is already proved as `dlAdicBasePrimeUnit`; its
proof derives characteristic from finite-field cardinality and uses the distinct
coefficient and characteristic primes. No new theorem or dependency module is needed.

## Second reading by W5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
