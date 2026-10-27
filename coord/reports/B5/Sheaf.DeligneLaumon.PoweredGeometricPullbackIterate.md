## What changed

Filled `AlgebraicGeometry.WeilSheaf.poweredGeometricPullback_frobeniusPowStr` by induction,
preserving its exact statement, its canonical carrier definition and its public imports.
Proved private composition and unit lemmas for pullback squares and extended the source
addition law to the zero second index. A private variant with a specified result index
keeps arithmetic rewrites outside concrete pullback functors. The induction is proved for
arbitrary scheme automorphisms and arbitrary families of
structure maps with the required composition laws. Explicit composition objects keep the
specialization from unfolding concrete pullback functors while matching the induction result.
The specialization spells out both Frobenius automorphisms instead of using local let aliases;
this avoids an otherwise expensive kernel conversion. Local irreducibility settings for
`upperStarFactor` and `frobeniusPowStr` keep their implementations abstract during that proof
and expire with the module.
It pastes the first square with the preceding square and combines the source blocks of length r. The actual theorem supplies
those laws from the source library. Substitution of the zero structure maps and the final compositor
cancellation are also proved with functors kept abstract.

Added the completely proved helper module
`Sheaf.DeligneLaumon.PoweredGeometricPullbackFirstStructure`, whose single public theorem
computes the first structure square directly from the explicit powered functor. Its helpers
keep functors and output objects abstract, so the kernel avoids expanding concrete sheaf
pullback constructions when checking equal carriers. It has zero holes.
The item imports it only for its proof. The helper uses a proof-only import of
`WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence`.
The item also imports `StalkCharpoly` for its proof of the zero case.
Updated the item's DAG proof and added the helper's node.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.WeilSheaf.poweredGeometricPullback_frobeniusPowStr`
(node `lem-zl-powered-geometric-pullback-iterate`).
One hole closed, zero holes added, zero split-off sorry statements, zero sorries left in
this delivery. All new private helpers and the public first-structure helper are proved.
Both modules compile cleanly together with `lcompile.py --all`, with no warnings.
The public theorem statement, canonical carrier definition and original public imports
were compared verbatim against the shared source and are unchanged.

## No longer needed

None. Both original declared proof dependencies remain used, and the helper refines the
first-map step of the original plan. No original public imports, nodes or modules were
removed or withdrawn. The blueprint unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The item was initially absent from the live Lean tree because it was quarantined, as
recorded in `coord/rework.tsv`; its archived source was restored. It has since also been
restored in the shared tree. Its absence was not treated as withdrawal.
The source addition lemma requires a positive second index, although this theorem permits
`r = 0`; a proved private unit-case extension supplies that boundary case.
Concrete pullback constructions can trigger kernel timeouts even in short naturality and
cancellation arguments. The proof uses generic functor calculations and keeps concrete
compositor equalities separate. No shared definitions or interfaces were changed.

## New nodes

`lem-zl-powered-geometric-pullback-first-structure`, realized by
`AlgebraicGeometry.WeilSheaf.poweredGeometricPullback_firstStructure` in
`Sheaf.DeligneLaumon.PoweredGeometricPullbackFirstStructure`. This is the first-map portion
of the original proof, with a complete Lean proof and no sorry. It was placed in a separate
module to keep each file below the compilation time limit.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
