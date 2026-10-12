## What changed

Proved `AlgebraicGeometry.Scheme.Modules.ModuleCohomologyFMapData.map_zero_augmentation`
in `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapZeroAugmentation`, preserving its signature
and imports. Added two proved private helpers: `forget_homologyπ` identifies the homology
projection under the forgetful functor, and `forget_augmentation` expresses the canonical
augmentation using an arbitrary injective resolution in abelian groups.

The main proof uses `D.sections` to identify the degree-zero sections comparison with the
identity. Cancelling the inclusion of cycles transfers `D.compatible` to cycles;
naturality of the homology projection transfers it to homology. Cancelling the resolution
comparison and the invertible vertical homology map gives the stated augmentation square.
This follows the originally assigned node's planned argument. The node and module are
restored because they disappeared from the base fetched by the delivery dry run.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.ModuleCohomologyFMapData.map_zero_augmentation`
(node `lem-weil-pbc-module-cohomology-fmap-zero-augmentation`).
Both private helpers are proved. No sorry remains in the delivered module; no holes added
or split off. This does not claim that every dependency of the module is sorry-free.

Local compilation and the axiom probe succeed within the single-file limit. The first
delivery dry run found that the refreshed base no longer contains this assigned module
or node, so the delivery also documents their restoration. No holes are added relative
to the refreshed base; the one hole closed is counted against the originally assigned file.

## No longer needed

No existing import, node or module is pruned. The previous attempt's sandbox-only module
`Sheaf.AlgebraicGeometry.ModuleCohomologyFMapZeroAugmentationCore` and its sandbox-only node
`lem-weil-pbc-module-cohomology-fmap-zero-augmentation-core` are discarded and not delivered.
The target needs no helper with an unproved resolution compatibility statement.

## Where the brief, the DAG or earlier work was wrong

The prior report claimed a reduction while the target remained sorry, and the surviving
core helper only repeated `D.compatible`. It was not a completed reduction. The existing
DAG argument does work: Mathlib's homology-data comparisons supply the forgetful-functor
compatibility, and cycles inclusion plus homology projection naturality supplies the square.
No statement, definition, or unit route changes are necessary.

The first dry run refreshed to a base missing the original module and node. The change
record documents restoration of their original statement; no other module is adapted.

## New nodes

`lem-weil-pbc-module-cohomology-fmap-zero-augmentation` restores the originally assigned
node with the identical mathematical statement and a proof matching the completed Lean
argument. It has no sorry. This is restoration, not a newly split intermediate lemma.
Change record: `coord/changes/module-cohomology-fmap-zero-augmentation-reintroduction.md`.

## Second reading by N2

1. Interface: the repository version is absent (`diff` reports no such file), as the
   restoration record declares. Compared the delivery with the retained original in
   the V2 `ModuleCohomologyFMapBasicProperties` sandbox: the existing theorem signature
   is byte for byte identical. The diff adds only two private proved helpers, local
   elaboration options, and the proof. No definition, hypothesis, conclusion or target
   changes. Verdict: pass, with the declared restoration requiring CODEX review.
2. Proof: compiled the delivered module locally through `lcompile.py` without errors
   or warnings (27.3 seconds). A scratch copy with `#print axioms` for both helpers and
   `ModuleCohomologyFMapData.map_zero_augmentation` compiled (27.9 seconds); all three
   use exactly `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`. Scanned
   for sorry and forbidden declarations: none. There is no new data construction or
   witness selection. Verdict: pass.
3. Split statements: none. Both private helpers are fully proved and strictly smaller
   comparison identities. Checked zero morphisms and zero complexes: the argument
   only uses functoriality, monic cycles inclusions and isomorphism cancellation, so
   these cases require no nonzero assumptions. Independent search for
   `homologyπ_comp_homologyIso|π_comp_homologyIso_inv|toRightDerivedZero.*comp` found
   Mathlib's homology-data projection identities and resolution augmentation identity,
   which the proof already uses. The library's `LeraySectionsResolutionComparison`
   contains the same forgetful projection identity only as a private helper; it is
   unavailable for reuse and importing that larger module would not shorten this
   proof. No new public intermediate statement or restatement. Verdict: pass.
4. Route and pruning: read `ModuleCohomologyFMap` in full and checked the cycles square,
   homology square and the final cancellations against its actual map definition.
   Mathlib's augmentation naturality for one functor does not directly identify the
   two schemes' sections functors and the auxiliary complex K; this proof supplies
   precisely that comparison from `D.sections` and `D.compatible`. The sole public
   import is needed by the statement itself. No proof-only public import, unused
   import, or old dependency to prune. Checked `dag/units/sk-thm-p1.json`: no realized
   statement or step is bypassed or changed. Verdict: pass.
5. DAG: its three proof steps match the two helpers, the cycles-to-homology square,
   and cancellation. `proof_deps` is the union of the stated uses: the map data and
   module cohomology definitions. Its source and agent proof origin match the
   construction. The restored node has chapter, unit, creation, blueprint, searches,
   and Lean records; its Lean signature matches the file. Verdict: pass.

Second reading changed only this report, adding the independent checks and their
verdicts. The Lean proof, node and restoration record required no repair. The delivery
closes 1 of 1 holes in the originally assigned module, adds 0 and splits off 0; because
that module is absent on the refreshed base, this restoration does not claim a net
hole decrease in the refreshed targets' import closure.
