## What changed

Restored the quarantined module `Sheaf.AlgebraicGeometry.UnboundedAbelianExchangeComparison`.
Removed its private import of `WeilConjectures.AlgebraicGeometry.ModuleAbelianUnderivedExchange`,
which imports upstream coefficient comparisons colliding with the retained
`Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison` declarations.
Reproved the ordinary exchange identity and its unit identity as two private helpers,
using the existing upstream theorem's argument against the retained coefficient interface.
All three original public declarations, their signatures, both public definition bodies,
and the original derived-descent proof are preserved.

Updated the item's proof node to describe this private ordinary argument.
Change record: `coord/changes/C4-unbounded-abelian-exchange-import-repair.md`.

Validation: the complete restored module compiled successfully via `lcompile.py` in 40 seconds.
The repair preserves arbitrary rings, arbitrary complexes, and all square hypotheses;
the ordinary helper requires only a commutative square, as before.

## Proved and sorry left

This is a zero-hole import repair. Original holes: 0; holes closed: 0; holes added: 0;
holes left in the delivered module: 0. Nothing was split off.

Preserved the complete proof of
`AlgebraicGeometry.Etale.unbounded_abelian_exchange_comparison`
(node `lem-kun-unbounded-abelian-exchange-comparison`).
Added fully proved private helpers `moduleAbelianUpperStarIso_unit` and
`moduleAbelianUnderivedExchange_compatibility`.
The existing imported dependencies retain their own proof status; this packet adds no holes.

## No longer needed

Removed the proof import `WeilConjectures.AlgebraicGeometry.ModuleAbelianUnderivedExchange`.
The proof no longer needs the declaration attached to
`lem-weil-pbc-module-abelian-underived-exchange` as an imported dependency: its ordinary
argument is proved privately from the retained coefficient comparisons and
`def-weil-pbc-underived-exchange`. The upstream declaration remains untouched.
The upstream `ModuleAbelianCoefficientComparison` and
`ModuleAbelianDerivedDirectImageComparison` modules are consequently not introduced
into this module's environment by that proof import.
No modules are withdrawn, and all remaining mathematical dependencies and the unit route remain.

## Where the brief, the DAG or earlier work was wrong

The quarantine diagnosis is confirmed: the upstream ordinary-exchange module brings in
upstream declarations named `moduleAbelianUpperStarIso` and `moduleAbelianForget`, while
the retained Sheaf comparison module already defines them. The old proof import therefore
fails before proof elaboration. The mathematics and public statements require no correction.
`downstream.py --allow-missing --uses` finds zero live consumers because the item is quarantined;
the change record also inventories its eight archived direct consumers. Their restoration
remains with their rework items, and this packet preserves the interface they use.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
