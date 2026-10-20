## What changed

Retired Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherentSupportPart in favour of
WeilConjectures.AlgebraicGeometry.RHomSupportedQuasiCoherentSupportPart, as listed in
coord/retire-items.tsv and requested by the human's 2026-10-20 retirement instruction.
Changed the one consumer, Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherent, by replacing
its plain support-part import. Its statement, proof, and public imports are unchanged.
Updated lem-sc-rhom-supported-qcoherent-support-part's Lean attachment to the existing
upstream declaration. The upstream theorem and all adopted source files are unchanged.

Change record: coord/changes/retire-rhom-support-part-20261021.md.

## Proved and sorry left

The assigned module had zero textual sorries before this delivery. Holes closed: none;
holes added: none; split off: none. Its existing theorem
AlgebraicGeometry.rhom_supported_quasiCoherent_support_part remains available from the
upstream module. No sorry is left in the changed consumer or introduced elsewhere.
This is duplicate retirement, not a newly proved theorem or a decomposition.

Compiled the original item (10.7 s) and the consumer after import migration (3.6 s),
through lcompile.py. The consumer uses the unchanged upstream theorem directly.

## No longer needed

Withdrawn module: Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherentSupportPart.
Its sole direct consumer no longer imports it. The node remains needed and now points
to the upstream theorem, preserving all DAG parent references and the unit route.
No mathematical dependency or unit is pruned; the three private zero-target helpers
remain in the adopted upstream proof. The original public-import environment of the
consumer is unchanged. No other module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an open proof, but this assigned module already
has a complete proof and zero textual holes. Its explicit retirement row supplies the
actual remaining task. The row classifies the upstream theorem as restated: comparison
shows the only signature difference is overFunctor.{u} versus overFunctor, with the
same inferred universe. The original consumer proof compiles unchanged against it.
The node's statement, proof dependencies, and the Picard unit route are unchanged.

Searched the source trees and DAG for the same declaration and found the existing
upstream copy; msearch LeanFinder returned only general derived t-structure results,
Loogle and grep found no additional homObj zero theorem. Read the source's support
observation in perfect.tex, Tag 0A9C. The existing argument covers the empty scheme,
empty and full support, and zero target: open restriction and cohomology detect zero,
and internal Hom into a zero object is zero.

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
