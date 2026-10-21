## What changed

Retired `Sheaf.CategoryTheory.FilteredCohomologyImage` by listing its path in `deleted.txt`.
Migrated the six current importers to `WeilConjectures.CategoryTheory.FilteredCohomologyImage`
and replaced standalone uses of `cohomologyImage` by `homologyFiltration`. The upstream
finiteness theorem is still called `cohomologyImage_isFinite`; its calls and all existing
proofs are retained. No target or upstream source was edited.

Updated the finiteness node's retirement note and the four presentation nodes' Lean
statement records. All mathematical statements and dependency routes are preserved.
The change record is `coord/changes/retire-filtered-cohomology-image-T1.md`.

Validation: all eight inventory/current consumers compile with `lcompile.py --all`,
including the six adapted files and the two unchanged current files. A source scan
confirms that every current import and standalone use of the retired interface is covered.

## Proved and sorry left

The assigned copy had zero proof holes before retirement. Closed 0; added 0; split off 0;
remaining 0. No delivered consumer contains a `sorry`, and no definition is hollowed.
This packet is an API retirement, not a new proof claim.

## No longer needed

`Sheaf.CategoryTheory.FilteredCohomologyImage` and its abbreviation
`CategoryTheory.DecreasingFiltration.cohomologyImage` are withdrawn. Each of the six live
consumer imports is replaced by the upstream twin import. No other imports or modules
are pruned by this packet. The finiteness theorem remains attached to
`WeilConjectures.CategoryTheory.FilteredCohomologyImage`.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempted no retirement after the C1 compatibility repair. The current
explicit RETIRE instruction requires completing the migration and deleting that compatibility
module; the previous zero-hole repair does not satisfy that instruction.

The live importers include `FilteredPageTwoComparison`, which was absent from the inventory.
It is included in this packet. `FilteredHomotopySpectralSequence` no longer refers to the
retired copy and is compiled unchanged. During this session J1 retired
`FilteredStationaryCycleComparison` and changed its consumers to the upstream twin. This
packet was refreshed to preserve that landing: the empty module is compiled unchanged,
and `FilteredPageTwoComparison` keeps its current upstream StationaryCycleComparison import.

## New nodes

None.

## Forced adaptations

No currently held consumer is changed. All changes to live consumer Lean sources are the
exact import replacement and standalone-name substitution required by the explicit
retirement assignment. No extra imports, proof edits, or declaration renamings are included.
The old abbreviation reduces directly to `homologyFiltration`, so replacing it in the
consumer signatures preserves their elaborated types.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
