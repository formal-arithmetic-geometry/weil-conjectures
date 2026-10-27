## What changed

Restored `lean/Sheaf/Paper/ConstantComplexQuotientModel.lean` from the quarantine
path recorded in `coord/rework.tsv`. Added the priority-4000 instance
`AlgebraicGeometry.ConstantComplexBaseChange.siteSmall`, proved by
`essentiallySmallSelf.{0, u, u + 1}`, fixing coefficient-site smallness at `u + 1`.
Exported it alongside the existing fixed-size abelian sheafification instances.
No existing declaration, construction, signature, import or DAG field changes.
The repaired module compiles in 37.3 seconds; its unchanged direct importers
`ConstantComplexNormalizedReductions` and `ConstantComplexStrictBaseChangeData`
compile in 5.2 and 21.3 seconds respectively. The other unchanged archived
consumers `ConstantComplexCompletedPullback`, `ConstantComplexFinitePullback`, and
`ConstantComplexStrictBaseChange` compile in 2.8, 2.9, and 30.9 seconds. All five
validation copies were verified byte-identical to their archives and removed
before delivery.

Change record: `coord/changes/G1-constant-complex-smallness-universe.md`.

## Proved and sorry left

Assigned compilation repair completed. The restored archive has zero `sorry`s;
the delivered module has zero. Closed holes: none (0 of 0). Added holes: none.
No decomposition and no split-off statements. The new instance is fully
proved from Mathlib. Existing instance and functor proofs are preserved verbatim.

## No longer needed

None. No import, declaration, module or node is pruned. The quarantined source is
restored with all its declarations and dependencies, including the existing
`ReductionData.tower` performance repair. The definition node retains its Lean
attachment. No unit route changes.

## Where the brief, the DAG or earlier work was wrong

The item is a zero-hole compilation repair, rather than an unfinished theorem.
The archived module disabled some generic smallness instances but still allowed
`WeilConjectures.scalarReductionSiteSmall` to supply an unresolved universe in
coefficient sheaf operation synthesis. The fixed-size instance resolves
that inference without changing the generic instance or the mathematics.
The instance must be exported: a local-only version left the same universe error
at line 134 of `ConstantComplexStrictBaseChangeData`, which constructs additional
coefficient operations. Exporting it lets that unchanged consumer compile.

The live downstream search reports no importers because consumers are quarantined,
not withdrawn. The preserved sources identify two direct importers; they are
validated unchanged and retained in their archives, not deleted or delivered as
unchanged restoration copies. The existing node has no proof steps or proof
dependencies to revise, and its statement and Lean attachment are preserved.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
