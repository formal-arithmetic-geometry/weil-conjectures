## What changed

Repaired the return of delivery 9f5dc5c71d3: the landing tools refused it because
the item file was created after base 417a2271a. Read and copied the current lean/
file rather than treating the path as absent or restoring an older implementation.
Retained its canonical public import and complete module docstring, and added the
standard exposed public-section header. No quarantine path is edited or withdrawn.

The substantive repair is the stale DAG attachment:
new-t3-qcoh-tensor-resolution-chart-homology-naturality now records the canonical
WeilConjectures module with existing = true, rather than identifying the Sheaf
compatibility wrapper as the declaration's implementation. Rebuilt the node from
the current shared node, changing only lean. Its complete statement is byte-for-byte
identical to the current upstream theorem signature. Proof, proof dependencies,
source, unit route and all independent metadata are preserved.

Change record: coord/changes/D3-qcoh-chart-homology-naturality-canonical.md.

## Proved and sorry left

Zero original holes, zero holes closed, zero holes added, zero split off and zero
holes left. This is an assigned zero-hole metadata and compatibility-module repair;
no theorem is claimed as newly proved. The exported theorem is
AlgebraicGeometry.tensorResolutionChartHomologyIso_naturality, attached to
new-t3-qcoh-tensor-resolution-chart-homology-naturality. Its upstream proof first
establishes the pure-tensor square and then applies homology naturality.

On 2026-10-23, lcompile.py compiled the current wrapper successfully (6.1 s)
and the scratch consumer successfully (41.5 s), with no warnings.
A scratch consumer imports the repaired wrapper and the existing Sheaf coordinate-
sections naturality and chart-comparison naturality wrappers, applies the theorem
to the exact DAG signature, and checks the six principal theorem/definition axioms.
The scratch consumer is excluded from delivery.

The theorem includes n = 0, zero modules and the zero ring, and adds no flatness
assumption. No statement or data construction is introduced or changed.

## No longer needed

None. No import is removed from the current source, and no node or module is
withdrawn or declared globally unused. The canonical upstream proof continues to
use the affine tilde tensor, tilde-Gamma adjunction and associated-sheaf sections
facts. The DAG parent new-g2-existing-qcoh-tensor-resolution-coordinate-naturality
and all unit steps remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The retained report incorrectly said the current lean/ path was absent. It now
exists as a compatibility wrapper; the former quarantine path is currently absent,
and the current coord/rework.tsv has no row for the item. This repair starts from
that current file as the return requests. The current DAG attachment
still identified the wrapper as a newly implemented declaration; the declaration
already has its complete proof in the adopted source module. The corrected
attachment records that implementation without duplicating or weakening it.

The return concerned landing-base drift. The proof is not rewritten and no source-
library file is edited. The delivery tool builds the new packet on its freshly
fetched sheaf-dag base and performs the required compile and preflight checks.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
