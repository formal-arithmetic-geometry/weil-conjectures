## What changed

Restored lean/Sheaf/Paper/CondensedOpenClosedRecollement.lean byte for byte from the
quarantine path named by coord/rework.tsv. This repairs the missing library source while
preserving its theorem, private helpers, imports, DAG attachment and proof dependencies.
The complete archived proof compiles against the current published dependencies in
37.1 seconds, with no errors or warnings. No other Lean module is changed.

The proof uses abelian closed support, scalar-change equivalences, an explicit kernel
construction for the exceptional right adjoint, the existing bounded-below derived
adjunction API, the unique recollement triangle theorem, and functorial bounded
injective resolutions. LeanFinder, Loogle and local source searches found no single
replacement theorem for this combined condensed-coefficient assertion.

Change record: coord/changes/A3-restore-condensed-open-closed-recollement.md.
The consumer scan includes quarantined ordinary and import-all consumers; their
interfaces and private-helper access are preserved exactly.

## Proved and sorry left

The archived theorem
AlgebraicGeometry.ProEtale.CondensedRing.condensed_open_closed_recollement
(node lem-weil-pbc-condensed-open-closed-recollement) is already fully proved and restored
with all of its proved private helpers. The actual hole count is zero before and zero
after. Newly closed: 0 of 0. Added holes: 0. Split off: 0. No sorry remains in the
restored module. This delivery claims source restoration, not new net proof progress.

## No longer needed

None. No import, declaration, dependency node, module or unit proof step is pruned.
All dependencies and the original unit route are preserved.

## Where the brief, the DAG or earlier work was wrong

This is a quarantined-source restoration rather than an unfinished theorem: the preserved
source already has a complete proof. Its absence from lean did not withdraw its mathematics
or dependencies. The current rework row was followed and the existing Lean attachment
was retained. There is no item-specific return entry in coord/returns/A3.md.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
