## What changed

Retired `Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherentPseudoPart` in favor of the
complete upstream twin `WeilConjectures.AlgebraicGeometry.RHomSupportedQuasiCoherentPseudoPart`.
The duplicate module is listed in `deleted.txt`. Adapted the unclaimed direct consumer
`Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherent` by changing its proof import to the
upstream module; its declarations and proof are unchanged. Reattached the DAG node to the
upstream declaration. The change record is `coord/changes/M3-rhom-pseudo-part-retirement.md`.

## Proved and sorry left

This retirement contained zero textual sorries. It closes 0 sorries, adds 0, and leaves 0
sorries. The retained upstream theorem is already fully proved.

## No longer needed

The duplicate Sheaf module and its import are no longer needed. The upstream theorem
supplies the same declaration. No component proof dependency is removed from the DAG route.

## Where the brief, the DAG or earlier work was wrong

The queue listed this already-proved duplicate as a retirement item after the upstream
source twin was adopted. The source and duplicate theorem signatures differ only by explicit
universe annotations that are definitionally equal. No mathematical statement is changed.
The consumer adaptation is forced because the old imported module is withdrawn.

## New nodes

None.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
