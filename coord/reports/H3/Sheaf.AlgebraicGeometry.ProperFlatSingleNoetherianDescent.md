## What changed

Replaced the `sorry` in `AlgebraicGeometry.properFlat_single_noetherian_descent`
by a proof with the unchanged signature. Its private, fully proved helpers descend
the proper morphism to a stage and transport relative flatness across the canonical
scheme isomorphism. The proof constructs the affine neighbourhood, the integer-subalgebra
approximation, the cartesian comparisons and the ordinary tensor-pullback isomorphisms.
It realizes the original unit's Noetherian-approximation step.

Added one module, `Sheaf.AlgebraicGeometry.FlatModuleOnLaterStage`, for the remaining
fixed-model sheaf descent step. The target imports it, `EventuallyProper`, `RelativelyFlatModulePullback`,
`TensorPullbackFinitePresentation` and `AffineTransitionLimit` privately.
The integer-subalgebra colimit declarations arrive through the latter public import.
The new statement has no properness, neighbourhood, source approximation or direct-image
assertion: it descends only the sheaf on a previously fixed source model. The proper
stage is constructed independently in the item's proof, and all later base changes
remain proper. No existing signature or public import was changed.

## Proved and sorry left

Closed: `AlgebraicGeometry.properFlat_single_noetherian_descent`
(node `lem-pc-proper-flat-single-noetherian-descent`). There are no sorries in the item.

Added: `AlgebraicGeometry.exists_flat_module_on_later_stage`
(node `lem-pc-flat-module-on-later-stage`), in the new module. Its entire proof is
`:= by sorry`, and its docstring explains finite-presentation descent, flatness descent
and the comparison isomorphism. This delivery is a decomposition: one upper hole closed,
one strictly smaller hole added, net zero new hole progress. The unchanged imported
properness-descent and relative-flatness declarations may still depend on their own holes.

The new statement includes the zero module, empty source, zero rings and a singleton
index set. Its input index excludes an empty index set. No transition-map flatness is
assumed. Finite presentation implies quasi-coherence, as required by Stacks 05LY.
All witnesses selected in this delivery occur in theorem proofs; no definition selects
data from an unproved existence theorem.

## No longer needed

The original node's dependency `lem-pc-noetherian-approximation-data`, module
`Sheaf.AlgebraicGeometry.NoetherianApproximationData`, is no longer needed for this item.
It was not imported in the original file, so no existing import was removed.
The redundant direct proof import
`WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits` was removed in second
reading: `AffineTransitionLimit` publicly imports it. The latter remains necessary for
scheme finite-presentation descent. In particular this proof does not need its perfect-object descent or derived-pullback
comparison: `lem-pc-filtered-cartesian-perfect-descent` /
`Sheaf.AlgebraicGeometry.FilteredCartesianPerfectDescent`, or the bounded-complex
comparison from `lem-pc-filtered-cartesian-flat-complex-descent` /
`Sheaf.AlgebraicGeometry.FilteredCartesianFlatComplexDescent`. They may remain needed by
other items; this is pruning of this item's route only.

Retained `lem-weil-pbc-eventually-proper` / `Sheaf.AlgebraicGeometry.EventuallyProper`.
Scheme spreading-out and affine integer-subalgebra approximation are still used through
the existing proved source library. Single-module finite presentation and flatness
descent remain required in the new node; they are not claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The planned `noetherian_approximation_data` declaration requires perfect derived data
and global `HasDerivedCategory` assumptions absent from this geometric single-sheaf item.
A fixed-source ordinary sheaf descent statement suffices instead. The original unit's
approximation step and eventual properness are retained.

Existing `FlatModuleDescent`, `FlatModuleDescentPreorder`, `FlatBoundedComplexDescent`
and `PullbackModelFlatnessComparison` cannot be imported into this item: their public
import of `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage` creates a cycle.
The common return path is DirectImage -> DirectImage.FiniteFreeComplex -> ProperFlatCechModel
-> ProperFlatCohomologyModel -> ProperFlatCohomologyProperties -> ProperFlatFinitePresentationModel
-> ProperFlatBoundedPresentationModel -> ProperFlatAffineCechPerfectModel
-> FiniteAffineCechModelPerfect -> ProperFlatSingleDerivedDirectImagePerfect
-> ProperFlatSingleOpenPseudoCoherent -> ProperFlatSingleOpenNoetherianComparison
-> this item (all unqualified names here are Sheaf.AlgebraicGeometry modules).
`tools/import_direction.py may` confirmed the obstruction. No other group's module was
adapted to work around it. The new fixed-model result is not a copy of any of these
statements: it combines sheaf existence and flatness on the fixed-model subsystem, and
omits all geometry that this item's proof already supplies. The combined statement remains a genuine specialization of 01ZR and 05LY.
The lower modules `FinitePresentationModuleMapDescent`, `FlatModuleDescentAffineCharts`
and `AffineFlatModuleDescent` have no import cycle here; a later proof can use the former
for the object, then the latter two for the affine-chart argument. A direct application
of `FlatModuleDescent` or `StagedModuleEventualFlatness` is still blocked by the cycle.

The local literature tree lacks `stacks-project/limits.tex`. I read Stacks Tags
[01ZR](https://stacks.math.columbia.edu/tag/01ZR) and
[05LY](https://stacks.math.columbia.edu/tag/05LY), and verified their exact labels in the
public Stacks `limits.tex` source. Searches were run through `msearch.py`; LeanSearch
returned HTTP 500, LeanFinder found geometric flatness and finite-presentation predicates
but no descent theorem, and the Mathlib grep found no match. Blueprint searches for
flat module, finitely presented module, Noetherian approximation, and finite-presentation
flatness found no duplicate blueprint statement of the fixed-model combined result.

## New nodes

`lem-pc-flat-module-on-later-stage`, in
`dag/nodes/sec-picard-framework/lem-pc-flat-module-on-later-stage.json`, records the
fixed-model sheaf descent step with its source, proof, actual searches, and Lean statement.
The original node's `proof`, `proof_deps` and `proof_origin` now match the delivered route.
No change record is needed: no existing statement, definition or public command changed.
Private flatness-isomorphism helpers reuse the sectionwise argument of
`PullbackModelFlatnessComparison`; that module cannot be imported because of the cycle.

## Second reading by H3

1. **Interface: PASS.** Read both delivered modules and diffed the existing module
   against the repository. Programmatically compared the entire existing theorem
   signature before `:= by`: byte-for-byte identical. Its docstring, public imports,
   visibility and existing definitions are unchanged. Only private proved helpers,
   proof imports and the proof body were added. No change record is required.
2. **Proof and axioms: PASS as a decomposition.** Both files compiled individually
   through `lcompile.py --all` (21.3 and 16.8 seconds). Searched the delivered Lean
   for sorry and forbidden commands: exactly the one public named theorem
   `AlgebraicGeometry.exists_flat_module_on_later_stage` remains sorry. Printed axioms
   in a scratch copy for the main theorem, all four private helpers and the new
   theorem. Every helper uses only propext, Classical.choice and Quot.sound; the main
   and split theorem also use sorryAx. There are no definitions in this delivery
   selecting arbitrary data from existence theorems. All descent witnesses are
   local to theorem proofs. The upper declaration is reduced, not independently
   proved free of sorryAx; holes closed 1, holes added 1, net 0.
3. **Split statement: PASS.** Independently read Stacks Tags
   [01ZR](https://stacks.math.columbia.edu/tag/01ZR) and
   [05LY](https://stacks.math.columbia.edu/tag/05LY). The tail above i is cofinal;
   its fixed-source models are qcqs with affine transitions. Finite presentation
   implies quasi-coherence. Thus object descent followed by eventual relative
   flatness gives exactly the stated result and canonical module comparison.
   Checked singleton systems (j = i with the canonical comparison), empty sources
   and zero modules (the zero sheaf), and zero rings. No injectivity or flatness of
   transition ring maps is needed. The new statement has none of the neighbourhood,
   source descent, properness or Noetherian-source assertions of the original: it
   is strictly smaller, not a renamed restatement. Its sourced docstring and node
   are present. Independent msearch queries used Loogle `Module.Flat`, LeanFinder
   "A finite presentation quasi-coherent sheaf spreads out over an inverse limit
   of affine schemes and becomes relatively flat at a finite stage", and grep
   `finitely.*presented.*flat|flat.*finite.*stage|module.*limit.*descent`; no exact
   combined theorem was found. Read existing finite-presentation and flatness
   descent declarations and the upstream finite-descent file. The object-only
   theorem is usable here, but the geometric eventual-flatness theorem and its
   staged wrapper reach this item through DirectImage and cannot be imported.
   No closure of the remaining combined hole follows by a direct application.
4. **Route and pruning: PASS, with one repair.** Reviewed proper-stage descent,
   transport of the sheaf along the pullback isomorphism, horizontal cartesian
   pasting, the composition/identity comparison, and the final total-open base
   change. The Noetherian approximation step of sk-thm-picard-coherence remains
   in the proof. The unit's realized record is unchanged (its statement and step
   lists are already empty in the repository; no new realization is claimed).
   The original proof_deps are exactly noetherian-approximation-data and
   eventually-proper: the former is unused and reported, the latter is used.
   Removed the redundant private integer-subalgebra colimit import: it is publicly
   imported by the necessary AffineTransitionLimit module. Other added imports
   supply declarations used in the proof; all are private.
5. **DAG: PASS.** Parsed both node files, compared the existing node with the
   repository (only proof, proof_deps and proof_origin differ), and checked the
   new node's Lean statement exactly against its declaration. The new node has
   source, dependencies, proof steps, proof origin, search records, split status,
   created/blueprint records, chapter, unit and Lean record. The existing node's
   steps record the actual proper-first, fixed-sheaf-later reduction. The new
   node's dependencies record the finite-presentation/flatness descent argument
   for its open proof rather than claim those declarations are already applied.

Second-reading changes: removed one redundant private import and an extra blank
line, expanded the new theorem's docstring with the cofinal-tail and qcqs/affine
transition checks, corrected the import/pruning and next-proof discussion above,
and added this review. No signatures, definitions, public imports or proof bodies
were changed by the second reader.
