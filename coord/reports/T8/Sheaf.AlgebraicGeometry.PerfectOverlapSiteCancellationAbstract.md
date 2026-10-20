## What changed

Withdraw `Sheaf.AlgebraicGeometry.PerfectOverlapSiteCancellationAbstract` using
`deleted.txt`, completing its zero-hole retirement assignment. The current
library has no importer of this copy. All nine declarations shared with
`WeilConjectures.AlgebraicGeometry.PerfectOverlapSiteCancellationAbstract` have
identical signatures; the additional `AlgebraicGeometry.natIso_inv_map_hom`
has no users. The upstream module and every upstream declaration stay unchanged.

Change record:
`coord/changes/retire-perfect-overlap-site-cancellation-abstract.md`.

## Proved and sorry left

Proved 0 of 0 sorries: this is a retirement, not a proof or decomposition.
Holes closed: none. Holes added: none. Sorries left: none.
No new nodes, statements, definitions, or proof dependencies.

The server compilation of the scratch probe imports the upstream twin and
checks all nine replacement declarations and their axioms. None uses sorryAx;
only standard axioms occur. The probe is scratch work and is not delivered.

## No longer needed

Retire the whole module
`Sheaf.AlgebraicGeometry.PerfectOverlapSiteCancellationAbstract`, including its
unused extra lemma `AlgebraicGeometry.natIso_inv_map_hom`. Its public Mathlib
Equivalence import disappears with the unused copy; the upstream twin retains
its own import. No currently needed declaration or DAG node is pruned.

There are zero downstream modules, as checked with tools/downstream.py and a
full literal search of lean/. No DAG node has this module in its Lean record.
The four historical consumers now exist upstream and already use the upstream
twin. No consumer adaptation is needed.

## Where the brief, the DAG or earlier work was wrong

The generic stage-3 proof brief does not describe this queue row: its kind is
`retire`, with zero holes. The human's 2026-10-20 retirement instructions in
coord/changes/retire-sheaf-twins-20261020.md specify the actual work. The saved
retirement inventory still lists four old Sheaf consumers and describes
natIso_inv_map_hom as used by CoreComparisons. Current sources have no such
consumer: CoreComparisons already uses the upstream twin and no longer calls
the extra lemma. No DAG attachment or unit route requires alteration.

## Second reading by T8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
