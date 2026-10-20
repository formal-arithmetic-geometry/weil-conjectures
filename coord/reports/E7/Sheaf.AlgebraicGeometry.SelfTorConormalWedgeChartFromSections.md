## What changed

This is the explicit zero-hole retirement assignment in `coord/retire-items.tsv`.
The duplicate `Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChartFromSections`
module is withdrawn through `deleted.txt`; its complete theorem remains available
from the adopted `WeilConjectures` twin. The attached DAG node is repointed to that
upstream declaration. The sole direct consumer,
`Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChart`, privately imports the upstream
twin and transports its `exteriorPower` chart isomorphism through the proved
`exteriorSheafIsoExteriorPower` comparison. Its public statement and public imports
are preserved exactly.

The original consumer was compiled as a baseline, and the adapted consumer was
compiled with `lcompile.py`; the adapted file compiles cleanly with no warnings.
The three required searches were run with `msearch.py`: local grep found no exact
additional theorem, LeanFinder found only general exterior/Kähler APIs, and Loogle
found no exact self-Tor chart theorem. The adopted upstream twin is the exact
existing result, so no new proof is introduced.

Change record: `coord/changes/E7-retire-self-tor-conormal-wedge-chart-from-sections.md`.

## Proved and sorry left

The item had zero initial holes and remains zero-hole after retirement: 0 of 0
sorries closed, 0 added, 0 split off, and 0 left. The complete theorem is preserved
in the adopted upstream twin. The adapted consumer retains its complete proof and
its public theorem `AlgebraicGeometry.exists_selfTor_conormal_wedge_chart`.
No `sorry`, axiom, or new declaration is introduced.

## No longer needed

Pruned the duplicate module
`Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChartFromSections` and the consumer's
private import of it. The consumer's prior direct application through the Sheaf
`exteriorSheaf` encoding is replaced by the upstream `exteriorPower` theorem plus
the existing canonical comparison; the duplicate module's private helpers and
proof imports disappear with its withdrawal. No mathematical DAG node or unit
step is pruned: the node now points to the upstream theorem and all parent edges
remain valid. The transitive chart modules remain needed.

## Where the brief, the DAG or earlier work was wrong

The generic stage-3 brief describes a module with remaining `sorry`s, but this
queue row is an explicit retirement assignment and the source already has a
complete proof. A direct import replacement is insufficient because the upstream
statement uses `exteriorPower`, whereas the surviving consumer statement uses
`exteriorSheaf`. The proved comparison isomorphism supplies the necessary transport
without changing the consumer's public interface. The upstream source and all
mathematical dependencies remain unchanged; no unit route is bypassed.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and
the maintainer's independent review is the only review.
