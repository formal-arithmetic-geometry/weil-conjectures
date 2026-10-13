## What changed

Replaced the proof of `AlgebraicGeometry.relativeMV_pinned_vertex_comparisons` in
`Sheaf.AlgebraicGeometry.RelativeMVPinnedVertexComparisons`, preserving its signature and
existing docstring. Two proved private categorical helpers transport biproduct lifts and
signed desc maps through additive functors and component isomorphisms. Additivity of the
three derived functors used here follows locally from their existing adjunctions; no global
instance or existing interface changed.

Added `Sheaf.AlgebraicGeometry.RelativeMVExactOpenComparison`. Its definition
`AlgebraicGeometry.relativeMVExactOpenIso` explicitly maps the left-adjoint uniqueness
comparison and composes with `relativeMVImageComp`. It chooses no data from a new existence
hole. The unit identity `AlgebraicGeometry.relativeMVExactOpenIso_unit` is proved directly
from `Adjunction.unit_leftAdjointUniq_hom_app`. Restriction coherence along a single inclusion
is proved by cancellation of the exact-open unit after restriction to the smaller open.
Private helpers derive full faithfulness of open direct image, prove invertibility of the
restricted unit, and establish the generic restricted-counit/unit identity.

Added `Sheaf.AlgebraicGeometry.RelativeMVInverseOpenComparisons`. Its single theorem gives
comparisons on individual inverse-image opens with their unit, restriction, and pasted-mate
identities. This is used as an existential witness only inside the main theorem's proof;
there is no definition choosing its data. The main theorem constructs the source comparisons,
constructs the two middle comparisons with `mapBiprod` and `biprod.mapIso`, proves all four
row equations by categorical assembly, and specializes the open pasting equation at the overlap.

Added proof-only imports of `RelativeMVInverseOpenComparisons`,
`Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`, and
`Mathlib.CategoryTheory.Adjunction.Limits`. Local proof terms enable Mathlib's
existing finite-to-binary-biproduct preservation bridge. Updated the item's proof route and
added the two intermediate nodes. No existing module besides the assigned item was adapted.

All three modules compile using lcompile.py. The main module compiled without warnings in
28.3 seconds in the final standalone check before packaging. The edge cases W=U, empty
opens, U=V, and zero objects/maps introduce no division, nonemptiness, or cover premise;
the two new statements use the same adjunction formulas in those cases.

## Proved and sorry left

Closed the original textual hole in
`AlgebraicGeometry.relativeMV_pinned_vertex_comparisons`
(node `lem-pc-relative-mv-pinned-vertex-comparisons`). There are no holes left in the assigned
module. Also proved `AlgebraicGeometry.relativeMVExactOpenIso_unit` and the two private
biproduct transport helpers.

Added exactly one hole, the whole proof of a named public theorem:

- `AlgebraicGeometry.relativeMV_inverse_open_comparisons`, node
  `lem-pc-relative-mv-inverse-open-comparisons`, module `RelativeMVInverseOpenComparisons`.

This is a decomposition, not a complete proof with only the three allowed axioms. One upper
hole is closed and one lower hole is added (net zero holes). Also proved
`AlgebraicGeometry.relativeMVExactOpenIso_restriction` without introducing a hole for it.
The remaining theorem concerns individual inverse-image opens and their maps; it contains
neither the source row nor any biproduct or triangle. It is not the original theorem under
a new name. The main proof supplies the source comparisons, both source arrow identities,
and the full signed biproduct assembly.

## No longer needed

None. Both original public imports remain necessary for the original statement. No module
is certified pruned from the targets' import closure by this delivery. Direct dependencies
`def-pc-derived-base-change-map` and `lem-pc-ringed-spaces-derived-pullback-composition` move
from the item's direct proof dependency list into the inverse-image-open node; they remain needed
transitively and are not claimed as pruned. No cone presentation, boundary completion,
distinguishedness, affine hypotheses, compactness hypotheses, or cover lemma was imported.
The added Mathlib and Sheaf imports are used by the proof.

## Where the brief, the DAG or earlier work was wrong

The DAG's original steps describe long coherence calculations but its listed declarations
provide constructions rather than the exact nested-restriction or pasted-mate equations.
The inverse-image-open theorem states the remaining individual-open calculations. The
source-open theorem is proved by unit cancellation, avoiding the originally planned
exact-versus-derived nested-composition calculation. Existing declarations with
` sorry ` in their dependencies were not treated as an obstacle.

The shared adjunctions are compatible: `canonicalPullbackAdjunction` and `relativeMVAdj`
select `exists_schemeDerivedAdjunction` using the same counits selected from
`exists_derivedPullbackComposition`. No independent adjunction is substituted.

The cited local literature TeX is absent from this checkout, so the relevant source was read
on the official Stacks pages: https://stacks.math.columbia.edu/tag/08BV,
https://stacks.math.columbia.edu/tag/08HZ, and https://stacks.math.columbia.edu/tag/08HY.
The first two provide the exact-restriction presentation; the last provides the counit-mate
construction. The expanded coherence arguments are recorded as agent expansions, not quoted
as additional explicit lemmas in those sources. LeanSearch returned Internal Server Error;
LeanFinder, Loogle, Mathlib source reading, and searches of both library roots were completed.

The unit record `sk-thm-picard-semicon` has empty realized statement and step lists. This
comparison is below the unit level; its exact-restriction and pinned-base-change route is
retained, with no bypass of a realized unit statement or step.

## New nodes

`lem-pc-relative-mv-exact-open-comparison`, in
`dag/nodes/sec-picard-framework/lem-pc-relative-mv-exact-open-comparison.json`, records the
explicit source-open comparison, its proved unit formula, and its proved individual
restriction-coherence theorem. The module is
`lean/Sheaf/AlgebraicGeometry/RelativeMVExactOpenComparison.lean`.

`lem-pc-relative-mv-inverse-open-comparisons`, in
`dag/nodes/sec-picard-framework/lem-pc-relative-mv-inverse-open-comparisons.json`, records the
inverse-image-open comparisons with units, restriction along a single inclusion, and the
pasted base-change identity at one open. The module is
`lean/Sheaf/AlgebraicGeometry/RelativeMVInverseOpenComparisons.lean`.

No existing definition or statement changed, so there is no change record or forced adaptation.

## Second reading by T4

1. **Interface and accidental changes.** Compared the delivered item module with the repository version. The target theorem signature and all existing declarations are byte-for-byte unchanged; only proof imports, private helpers, and the proof body differ. The two added modules and DAG nodes are explicitly listed above.

2. **Compilation and proof status.** Compiled all three sandbox modules with `lcompile.py --all`, and recompiled the item standalone. They compile without errors or warnings. The item theorem and exact-open comparison declarations have no `sorry`; the only remaining `sorry` is the named public theorem `relativeMV_inverse_open_comparisons`, documented with its source and proof plan and represented by its DAG node. No forbidden declarations or hollow definitions occur.

3. **Truth and strength of split statements.** Checked the exact-open and inverse-open statements against their defining formulas, including empty opens, equal opens, zero maps, and arbitrary object maps. The inverse-open theorem is a strict lower-level coherence statement: it supplies only per-open comparisons, unit/restriction identities, and one pasted-mate identity, and does not restate the pinned-vertex theorem or assert biproduct/triangle conclusions.

4. **Shortest route and pruning.** The main proof uses the existing adjunction and biproduct lemmas first, with only local categorical transport helpers. The exact-open restriction proof cancels an isomorphic restricted unit; the pinned proof assembles the four row equations by `mapBiprod` and `biprod.mapIso`. All imports are used, and no old proof dependency is removable from the target closure.

5. **DAG and unit agreement.** Updated node proof routes and dependencies match the Lean proof and the two new split nodes carry complete statements, sources, proof plans, and Lean records. The route remains below the Picard unit and retains its exact-restriction and pinned-base-change steps; no realized unit statement or step is bypassed.

**Changes made during second reading.** No Lean or DAG repair was necessary after compilation and interface comparison. Added this second-reading record required by the delivery contract.
