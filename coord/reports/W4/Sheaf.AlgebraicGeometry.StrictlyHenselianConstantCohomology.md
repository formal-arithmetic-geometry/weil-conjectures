## What changed

Proved `AlgebraicGeometry.Etale.constantSheaf_cohomology_of_isStrictlyHenselianLocalRing`
in `Sheaf.AlgebraicGeometry.StrictlyHenselianConstantCohomology`, following both existing
DAG proof steps without changing any signature, definition, import, or dependency.
The component at `A` of `nonempty_constantSheaf_cohomology_zero_iso R` supplies degree
zero. The vanishing clause of `strictlyHenselian_etale_acyclic R inferInstance` applies
to the constant sheaf; `omega` converts positive natural degree to integer degree at least one.
The file compiled through `lcompile.py` in 3.4 seconds without diagnostics.

## Proved and sorry left

Closed one of one holes:
`AlgebraicGeometry.Etale.constantSheaf_cohomology_of_isStrictlyHenselianLocalRing`
(node `sbc-lem-strict-henselian-constant-cohomology`).
No `sorry` remains in the item module; no holes or modules were added. This is a proof
from the existing declared dependencies, not a decomposition. The existing dependency
`AlgebraicGeometry.Etale.nonempty_constantSheaf_cohomology_zero_iso`
(node `lem-sbc-strict-henselian-constant-hzero`) remains unproved in its own unchanged
module; thus the resulting theorem still depends transitively on that existing hole.

## No longer needed

None. Both existing proof imports and both DAG proof dependencies are used. All public
imports serve the unchanged statement. The unit `sk-rem-rest` has no additional realized
statement or proof steps to bypass. No nodes, modules, or maintainer approvals are pruned.
LeanFinder found generic cohomology results rather than a matching strictly henselian
constant-sheaf theorem; Loogle confirmed `Nat.cast_le`; local searches confirmed the
planned existing declarations supply both clauses directly.

## Where the brief, the DAG or earlier work was wrong

No correction needed. The declared proof dependencies fit the original statement exactly,
including its universes. Finiteness and invertibility are retained as given; the general
dependency statements do not need them. The existing DAG proof and proof-origin metadata
already describe the implemented argument, so no node change is necessary.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
