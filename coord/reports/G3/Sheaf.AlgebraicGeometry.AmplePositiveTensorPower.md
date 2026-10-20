## What changed

The assigned module is withdrawn through `deleted.txt`, completing the listed retirement
of the duplicate Sheaf module. The public theorem remains provided by the proved upstream
module `WeilConjectures.AlgebraicGeometry.AmplePositiveTensorPower`; no downstream importer
still imports the retired module. The upstream replacement and the canonical withdrawn stub
both compile through lcompile.py.

## Proved and sorry left

Holes closed: zero. Holes added: zero. Holes remaining in the assigned module: zero.
The upstream module already contains a complete proof of
AlgebraicGeometry.Scheme.Modules.isAmple_positive_tensorPow.
There is no new theorem, decomposition, or repair in this session.

## No longer needed

The Sheaf duplicate is withdrawn by this packet. All three listed consumers,
Sheaf.AlgebraicGeometry.GluedComponentAffineSection,
Sheaf.AlgebraicGeometry.NoetherianFibreAmpleNeighbourhood, and
Sheaf.TraceFormula.GradedImmersionAmpleCriterion, already import the upstream module.
No source under lean/Sheaf, lean/WeilConjectures, or quarantine imports the retired module.
No DAG node or unit still references its old module attachment; the node
lem-sc-ample-positive-tensor-power attaches the upstream theorem and records its proof.
No additional pruning is proposed.

## Where the brief, the DAG or earlier work was wrong

The dispatcher assigned a retirement that had already landed in
`coord/changes/retire-ample-positive-tensor-power-S4.md`; the live queue still lists it.
This packet uses the supported withdrawal mechanism so the delivery records an actual
retirement change rather than a compiling no-op. No new defect or theorem is introduced.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
