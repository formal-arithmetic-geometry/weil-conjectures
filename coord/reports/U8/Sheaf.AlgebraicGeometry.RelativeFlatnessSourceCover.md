## What changed

Proved `AlgebraicGeometry.relative_flatness_source_cover` in
`Sheaf.AlgebraicGeometry.RelativeFlatnessSourceCover`, preserving its full statement.
The pointwise equivalence follows from faithful flatness of the local stalk map,
the existing tensor-pullback stalk isomorphism restricted to the base ring, and
`Module.Flat.iff_flat_tensorProduct_of_faithfullyFlat_extension`. The cover clause
uses the existing two relative-flatness stalk criteria and joint surjectivity.

Added the private proof import `Sheaf.AlgebraicGeometry.TensorPullbackQuasiCoherent`
for its proved tensor-pullback quasi-coherence instance. Updated the item's proof
steps and proof dependencies to record that existing canonical comparison. All public
imports and signatures are preserved. The unit route is preserved; no unit step is bypassed.

Validation: the complete proof compiled through `lcompile.py` (5.8 seconds, no warnings).
The import-direction check permits the tensor-pullback comparison import.
Edge cases remain covered: zero modules, empty schemes, and an empty index type
(the surjectivity hypothesis then forces the target to have no points).

## Proved and sorry left

Closed 1 of 1 item holes:
`AlgebraicGeometry.relative_flatness_source_cover`
(node `lem-trf-relative-flatness-source-cover`).
No sorry remains in the item; no holes were added or split off.

The proof uses the existing holed dependency
`Module.Flat.iff_flat_tensorProduct_of_faithfullyFlat_extension`
(node `lem-trf-flatness-faithfully-flat-extension`), unchanged in this delivery.
This is a proof from the stated dependencies, rather than a claim that their
entire transitive axiom closure is already sorry-free.

## No longer needed

Removed the redundant private import
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`; the tensor-pullback
comparison module supplies the required quasi-coherence interface and already
imports it publicly. Its quasi-coherence theorem and node remain needed through
that comparison. No mathematical dependency node or module is pruned. All six
original proof dependencies remain used, directly or through that comparison.
No source-library declaration was removed or changed.

## Where the brief, the DAG or earlier work was wrong

The planned route works. Its quasi-coherence step names ordinary pullback, while
the item states tensor pullback. The existing canonical comparison and its proved
quasi-coherence instance supply this transport; the DAG now records that interface.
No statement correction or definition repair was needed.

Searches: LeanFinder returned the same-base faithfully flat tensor criterion,
which does not itself state intermediate-ring relative flatness. Loogle located
`Module.Flat.of_linearEquiv`. Mathlib/source searches located `stalkMap_comp`,
`Flat.iff_flat_stalkMap`, the two existing relative-flatness stalk criteria, and
the tensor-pullback comparison. The proof therefore follows the stated plan
without introducing any new results.

## Second reading by U8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
