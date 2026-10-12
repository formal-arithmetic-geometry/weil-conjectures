## What changed

Replaced the proof hole of
`CategoryTheory.grothendieckLeftEdgeMap_eq_hypercohomology` without changing its
statement or any existing definition. The proof now transports the truncation
spectral object along a prescribed-resolution comparison and uses
`Abelian.SpectralObject.leftEdge_naturality`.

Two private lemmas, `pageTargetComparison` and
`grothendieckLeftEdgeTargetIso_hom_app`, expand and identify the canonical target
comparison. Both are proved from the source library and naturality of
`rightDerivedZeroIsoSelf`; neither contains a hole. Their proof generalizes the
integer degree before specializing it, avoiding dependent proof casts.

Added the proof-only import
`Sheaf.CategoryTheory.GrothendieckResolutionUnitComparison`, a new module stating
only the ordinary-homology and composite-derived-unit compatibility needed for
the prescribed resolution. Updated the original node's proof, proof dependencies
and proof origin to match this route. Existing public imports are unchanged.

## Proved and sorry left

Closed the original hole in
`CategoryTheory.grothendieckLeftEdgeMap_eq_hypercohomology`
(`lem-pc-grothendieck-hypercohomology-edge`). Its complete Lean proof combines
source comparison, the proved target comparison, and spectral-edge naturality.
No sorry remains in the item's module. Both private comparison lemmas are proved.

Added one sorry:
`CategoryTheory.exists_grothendieck_resolution_unit_comparison`, in
`Sheaf.CategoryTheory.GrothendieckResolutionUnitComparison`, with node
`lem-pc-grothendieck-resolution-unit-comparison`.
This is a decomposition: one original hole closed and one strictly smaller hole
added, net zero. It is not a claim that the original theorem is now sorry-free.
The new theorem contains no edge map; it asserts the two canonical homology
components of a comparison constructed from the resolution augmentation and
derived units. The main proof supplies the target identification and edge
argument rather than restating the original conclusion as a hypothesis.

Both sandbox modules compile cleanly through `lcompile.py --all`. No definition,
axiom, target signature, or private holed declaration was added.

## No longer needed

Removed the proof imports:

- `Sheaf.CategoryTheory.GrothendieckSSDoubleComplexModel`, node
  `lem-pc-grothendieck-ss-double-complex-model`.
- `Sheaf.CategoryTheory.CartanEilenbergExists`, node
  `lem-sp-cartan-eilenberg-exists`.

Neither the double-complex model nor existence of a Cartan--Eilenberg resolution
is needed by this item's proof. Its associated filtration-model construction is
also bypassed here. This is a claim about this proof branch, not a claim that
other target branches no longer need those modules. No other import was removed.
The complex hypercohomology edge, composable-pair condition, and ordinary derived
comparison infrastructure remain needed. The unit record's realized statements
and steps are empty, so no protected unit realization was bypassed.

## Where the brief, the DAG or earlier work was wrong

The original proof plan uses a Cartan--Eilenberg model. The actual source-library
spectral object is defined by derived truncations, so naturality gives a shorter
route. A resolution comparison compatible with the composite derived unit is
still necessary; it is now isolated explicitly rather than silently assumed.
No statement was found false and no existing signature was changed.

An initially missing compiled dependency became available after the green cache
refreshed. The final validation uses the current green dependency cache, not a
locally rebuilt substitute for another worker's module.

## New nodes

`lem-pc-grothendieck-resolution-unit-comparison`, in
`dag/nodes/sec-picard-framework/lem-pc-grothendieck-resolution-unit-comparison.json`,
is the compatibility calculation on a prescribed injective resolution in Stacks
Project [Tag 015M](https://stacks.math.columbia.edu/tag/015M), with the abutment
identification of [Tag 015N](https://stacks.math.columbia.edu/tag/015N).
Its module is `Sheaf.CategoryTheory.GrothendieckResolutionUnitComparison`.
The docstring and node give the construction from the augmentation, the inverted
F-derived unit at the injective complex, and the map/extension comparison, then
explain both canonical homology equations. The equations determine precisely the
components used downstream; no definition chooses an unspecified witness.
Degree zero requires no positive-degree assumption or shift cancellation.
Zero objects and zero functors reduce the equations to the unique zero maps;
an arbitrary prescribed resolution is handled by comparison homotopy equivalences.
Three kinds of actual Mathlib searches and their results are recorded in the node.
No change record is required because no existing definition or statement changed.

## Second reading by P2

1. Compared the delivered item module with the repository version. The existing
   theorem signature is unchanged byte for byte; only its proof, private helpers,
   and proof-only imports differ. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`; no errors or warnings
   occurred. The item theorem has no `sorry`; the only remaining hole is the
   named public comparison theorem, with its matching node and docstring. Verdict:
   pass.
3. Read the split-off comparison statement and checked its degree-zero and zero
   functor cases. It asserts only the two homology compatibility equations used
   by the parent proof and does not restate the edge theorem. Verdict: true and
   appropriately strong.
4. Checked the proof route and imports against the source definitions. The
   truncation spectral object and edge naturality give a shorter valid route;
   the removed double-complex and Cartan--Eilenberg imports are unused. Verdict:
   pass.
5. Checked the DAG proof steps, dependencies, origin, and the new node's Lean
   record against the code. The unit route is preserved at the parent target;
   no realized unit statement or step is bypassed. Verdict: pass.

I changed only the proof route and its dependency metadata, added the required
   resolution/unit comparison module and node, and added this second-reading
   record. No target statement or existing definition was changed.
