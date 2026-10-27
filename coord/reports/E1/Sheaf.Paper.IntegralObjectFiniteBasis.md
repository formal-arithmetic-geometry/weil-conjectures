## What changed

Restored `Sheaf.Paper.IntegralObjectFiniteBasis` from the quarantine path in
`coord/rework.tsv`. Disabled the imported `WeilConjectures.scalarReductionSiteSmall`
instance for this file's elaboration, so typeclass search uses the private fixed-size
witness. Made its `essentiallySmallSelf` universes explicit as `{0, u, u + 1}`.

The existing construction of `WeilConjectures.IntegralObjectQuotient.finiteNormalizedBasis`
is preserved. Its scalar-extension basis, normalized object restriction comparison, and
single-complex argument still implement the four steps of
`lem-pur-integral-object-finite-basis`. The node's attachment, statement, and dependencies
are preserved, so no node edit is needed.

Change record: `coord/changes/E1-integral-object-finite-basis-universes.md`.

## Proved and sorry left

This is an assigned compile repair with zero original holes, zero holes closed, zero
holes added, and zero holes left in the item. The complete existing proof of
`WeilConjectures.IntegralObjectQuotient.finiteNormalizedBasis` remains in place.
No split-off statements were introduced.

The repaired item compiled without diagnostics in 42.2 seconds through `lcompile.py`.
A subsequent ordered consumer check compiled the item in 43.3 seconds and the unchanged
quarantined `Sheaf.Paper.IntegralObjectPullbackQuotientBasis` in 43.5 seconds. The temporary
consumer copy was removed afterward; it is not part of this delivery.

## No longer needed

None. No imports, declarations, nodes, modules, or proof dependencies were removed.
All four imports are used: the operations API and pro-etale localization supply the
public objects; the two proof imports supply scalar-extension and normalized
restriction/adjunction comparisons. No new mathematical route is proposed.

## Where the brief, the DAG or earlier work was wrong

The item source is absent from `lean/` because it is quarantined, not withdrawn. The
assignment is a zero-hole repair, rather than a remaining proof obligation. The
original error persisted after merely specifying the universes of `fixedSmall`:
`scalarReductionSiteSmall` also had to be removed from the file's instance search.
That attempt reproduced the listed universe failure and its cascading elaboration
errors; the completed repair compiled cleanly.

Loogle and LeanFinder both identify `CategoryTheory.essentiallySmallSelf` with result
universe `max w v u`. Its Mathlib source and the local fixed-universe uses confirm
`{0, u, u + 1}`. The existing DAG proof remains applicable without modification.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
