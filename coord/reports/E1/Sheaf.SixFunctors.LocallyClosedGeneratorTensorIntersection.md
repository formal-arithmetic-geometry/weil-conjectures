## What changed

Restored `lean/Sheaf/SixFunctors/LocallyClosedGeneratorTensorIntersection.lean` from
its quarantine archive and repaired the sync failure recorded in `coord/rework.tsv`.
The private `lisse_flat` proof now uses the public, fully qualified
`CategoryTheory.Mod.ResidueOrdinary.relativeTensorRightIso`, imported privately from
`Sheaf.Paper.IntegralResidueOrdinaryMonoidal`. This is the same balanced-coequalizer
comparison between `Mod.tensorLeft` and the monoidal right tensor functor.
All seven public declarations, their signatures and data, and all public imports
are preserved verbatim. The existing support-reconstruction proof and its DAG
route are retained. The final theorem now caches the normalized-comparison
existence proof as `h`, uses its witness for the homology properties, and reuses
`h` in the conjunction. This avoids repeating its expensive elaboration. The
final repaired file compiled without warnings in 35.8 seconds using `lcompile.py`,
with the normal 60-second limit.

Change record: `coord/changes/E1-generator-tensor-public-comparison.md`.

## Proved and sorry left

This is a repair of an already proved module: 0 original holes, 0 holes closed,
0 holes added, and 0 holes left. In particular,
`AlgebraicGeometry.ProEtale.CondensedRing.locallyClosedGeneratorTensorIntersection`
retains its complete proof (node
`lem-sfb-locally-closed-generator-tensor-intersection`). No statement was split off.

## No longer needed

Removed the proof-only `import all
WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian` and its dependence
on the old private comparison name. The public comparison is provided by
`Sheaf.Paper.IntegralResidueOrdinaryMonoidal`; the source Grothendieck module itself
remains a transitive dependency. No mathematical node or module is pruned, and no
existing source declaration is withdrawn. No change to the DAG route is needed
for this replacement of the tensor-comparison API.

`tools/downstream.py --allow-missing --uses` reports zero current importers or
consumers of any of the seven public declarations. A separate exact import scan
of both library roots and quarantine also finds zero importers. The DAG parent
`lem-sfb-admissible-tensor-constructibility` still needs the item, so its attachment
and dependencies are preserved and the module is restored, not withdrawn.

## Where the brief, the DAG or earlier work was wrong

The module is absent from the live Lean tree because of quarantine, not pruning.
The rework row identifies the old `Mod.relativeTensorRightIso` reference as
ambiguous after the upstream sync. The replacement uses an existing public
comparison with the required type, so no new mathematics or statement correction
is needed. The mathematical proof and unit route remain valid.

The first delivery attempt timed out in compilation and pushed nothing. Profiling
identified expensive type checking of derived comparison terms. Reusing the
comparison-existence proof in the final assembly removed duplicated work; the
final successful standalone compile took 35.8 seconds. No limit was raised, no
file was split, and all profiling and reduced-heartbeat experiments remain in
the sandbox scratch directory, outside the delivered source.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
