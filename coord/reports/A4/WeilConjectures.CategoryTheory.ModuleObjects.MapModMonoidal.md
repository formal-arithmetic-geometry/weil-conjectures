## What changed

Completed the ten existing coherence proof fields in
`WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal`, restoring the
coequalizer arguments recorded in the landed G4 change on the current source.
The two definitions are `CategoryTheory.Functor.mapModCoreMonoidal` and
`CategoryTheory.Mod.comapCoreMonoidal`.

Naturality follows after cancelling the relative tensor projection, using
naturality of the tensorator for mapMod and the projection equations for comap.
Associativity follows after cancelling two projections, using the underlying
associator and tensorator coherence. The unit axioms reduce to the coequalizer
desc equations for the explicit bimodule unitors. All comparison maps and
isomorphisms remain the actual existing constructions.

A programmatic comparison verifies that the complete source outside the ten
proof fields is byte-identical to the current library source. Signatures,
attributes, public imports, docstrings, visibility and construction data are
unchanged. No consumer adaptation is needed. Change record:
`coord/changes/A4-mapmodmonoidal-coherence-proofs.md`.

The item compiled cleanly with lcompile.py in 8.3 seconds, then in 5.7 seconds
in the verification batch. The unchanged direct consumers MonoidalModule and
UnitCoherence compiled in 5.1 and 6.5 seconds. The unchanged aggregate
WeilConjectures compiled in 51.7 seconds. TargetsCheck compiled in 34.2 seconds;
the final check explicitly loaded the repaired sandbox artifact and compiled
cleanly in 4.1 seconds.
Delivery preflight checks axioms.

## Proved and sorry left

Baseline: 10 holes; closed 10; added 0; split off 0; remaining 0.
The completed fields in each of
`CategoryTheory.Functor.mapModCoreMonoidal` and
`CategoryTheory.Mod.comapCoreMonoidal` are:

- `μIso_hom_natural_left`;
- `μIso_hom_natural_right`;
- `associativity`;
- `left_unitality`;
- `right_unitality`.

No sorry proof remains in the item or is added elsewhere. The earlier six
balancing and linearity theorem proofs are already complete in the current
source and are preserved verbatim, so they are not counted as holes closed.
The module docstring's historical mention of sorry is unchanged.

## No longer needed

None. No import, node, module or declaration is removed, and the original
coequalizer proof route is retained. No Sheaf dependency is introduced.
Searches by module and declaration name find no DAG attachment or blueprint tag
for this source module, so there is no node or unit record to update.

The shorter-route search found the complete prior library proofs in
`coord/changes/G4-mapmodmonoidal-restored-proofs.md` and reused them. LeanFinder
returned related monoidal-module and monoid-object declarations, without an
exact abstract module-transport theorem. Loogle did not resolve the abbreviated
query `Functor.CoreMonoidal`; the logged Mathlib grep found no matching names.

## Where the brief, the DAG or earlier work was wrong

The assigned red-build repair record is
`coord/repair-notes/WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal.json`
(job a61657403188e6f4, prior landing 8366ab1a09). It names only the aggregate
failures TargetsCheck and WeilConjectures with the error
`bad import 'WeilConjectures.PoincareDuality.Poincare'`.
The missing module is separately quarantined in coord/rework.tsv because it
imports Sheaf.Paper.FormalClosedSupportII. The current aggregate source files no
longer directly import that quarantined module. This packet restores no
quarantined source and changes no aggregate imports. The only edits are proof
fields of MapModMonoidal; the existing public interfaces and data are identical.

The downstream scan finds 787 importers. Only the item itself names
mapModCoreMonoidal; the item and UnitCoherence name comapCoreMonoidal.
MonoidalModule consumes the resulting monoidal instances. Both direct consumers
and both aggregate files named in the repair are checked unchanged against the
repaired module, to distinguish the old quarantine/import error from this proof
completion. No false mathematical statement or new proof dependency was found.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
