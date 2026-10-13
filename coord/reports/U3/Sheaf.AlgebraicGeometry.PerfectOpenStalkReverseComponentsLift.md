## What changed

Replaced the proof of `AlgebraicGeometry.Scheme.exists_perfect_open_stalk_reverse_components_lift`
without changing its statement or visibility. The proof extracts bounded support, explicitly
restricts each finite-free retraction using `sigmaComparison` and `overMapUnitIso`, indexes the
finite rectangle of degree pairs, applies a finite-family lifting theorem, and maps its natural
comparison to complexes. It defines the resulting components by cases and proves the zero
condition and every stalk equality. Outside the rectangle, preservation of zero objects proves
that the given stalk map is zero. The proof handles empty support intervals, including a > b.

Added the proof-only import `Sheaf.AlgebraicGeometry.FiniteProjectiveOpenStalkMapsLift` and
`Mathlib.Data.Int.Interval`. The new module publicly imports only the free-sheaf API and the open stalk API.
It states only a finite-family lifting fact about
module sheaves, with arbitrary targets and finite-free retract sources. It has no complexes,
boundedness, degree support or differential equations. The item's DAG proof now matches Lean.
The local transparency option is necessary for the open-subscheme point coercion in synthesis
of the stalk functor's existing zero-preservation instance. No definition or existing interface
was changed and no consumer adaptations are needed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.exists_perfect_open_stalk_reverse_components_lift`
(node `lem-sc-perfect-open-stalk-reverse-components-lift`). Its entire proof now compiles.

Added one hole:
`AlgebraicGeometry.Scheme.exists_finite_projective_open_stalk_maps_lift`
(node `lem-sc-finite-projective-open-stalk-maps-lift`), in the new module
`Sheaf.AlgebraicGeometry.FiniteProjectiveOpenStalkMapsLift`. Its whole proof is `by sorry`.
This is a decomposition, not a complete proof of the geometric argument: one original hole
closed, one strictly simpler geometric hole added, net zero holes. No sorry remains in the
item's module and no sorry is in a definition. Both delivered modules compile without warnings.

## No longer needed

No original imports or modules are pruned. Temporary imports of
`Mathlib.Data.Fintype.Sets` and `Mathlib.Data.Fintype.Prod` were removed after successful
compilation without them. Removing `Mathlib.Data.Int.Interval` fails because the integer
`LocallyFiniteOrder` instance is needed; this import is retained.

The item no longer directly depends on
`lem-weil-pbc-stalk-internal-hom-finite-presentation`
(`Sheaf.AlgebraicGeometry.StalkInternalHomFinitePresentation`); that geometric ingredient stays
in the new finite-family node's plan. Consequently it is not globally pruned and no unit route
is bypassed. `Sheaf.AlgebraicGeometry.FiniteFreeReverseComponentsLift` was inspected but not
imported: its open-subscheme pullback API and finite-free hypotheses differ from this item's
open slice-site stalk API and finite-projective retractions.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The original DAG's two steps combine a
geometric local lifting fact with a substantial bounded-complex assembly; these are now
separated. `OpenModuleStalkFunctor` defines the stalk functor and its preservation instances,
but does not expose the comparison-and-lifting theorem the original proof sketch needs.
The internal-Hom comparison is stated for ringed-space sheaves, so applying it on the open
slice site requires additional transport and representative-section glue. This missing glue is
recorded in the new geometric node rather than presumed available from the definition.

Searched Mathlib through LeanFinder, Loogle and grep, and attempted LeanSearch (HTTP 500,
recorded unavailable). LeanFinder returned finite-type generator APIs, ring spreading and
finite-presentation definitions; none states the new finite-family open-site lifting theorem.
Read the internal-Hom comparison and the finite-free reverse-component implementation.
Blueprint searches for finite stalk maps and for stalks found no duplicate statement of the
finite-family module-sheaf lemma. Read the source statements at Stacks Tags 01CP, 09RE and
0BC7. Tag 01CP is the direct source for representing maps locally; the other tags motivate the
finite-complex calculation. Edge cases checked: empty index family, zero source rank,
empty support rectangle, and arbitrary/non-finitely-presented targets. All are compatible
with the new statement and its proof in words.

## New nodes

`lem-sc-finite-projective-open-stalk-maps-lift` states simultaneous lifting of a finite family
of stalk maps from module sheaves that retract off finite free sheaves, on a common open
neighbourhood inside T. Its conclusion is module-level, and its targets are unrestricted.
The named remaining proof carries a complete finite-section/retraction argument and the
canonical comparison needed for the formula, sourced to Stacks Tag 01CP and the finite-matrix
arguments of 09RE/0BC7. The item supplies all complex, degree, boundedness and zero-support
assembly itself. No change record is required, since all existing signatures are identical.


## Second reading by U3

1. Compared the delivered item against the repository with diff and compared its
   full theorem signature byte for byte: identical. Visibility and the original
   public imports are unchanged. No definitions or other existing declarations change.
2. Compiled both modules locally. A scratch copy with `#print axioms` for both
   declarations reports only `propext`, `Classical.choice`, `Quot.sound`, and
   `sorryAx`, the last expected from the named remaining geometric lemma and open
   upstream proofs. Scanned both sources: the only sorry is the new named theorem;
   no forbidden declaration or hollow definition. The bounded-support proof uses
   functorial retractions, a genuinely finite square, and zero-source/target maps.
3. Read the new lemma and its complete docstring proof, checked Tag 01CP directly,
   and tested empty I, rank zero, arbitrary targets, and an empty support interval.
   The statement is true and is strictly the module-level geometric part, not a
   renamed complex theorem. Independent searches used LeanFinder for a finitely
   presented stalk homomorphism as a germ, Loogle for stalk restriction, and grep
   for representative germs and restriction isomorphisms. No direct duplicate was
   found. Read FiniteFreeLocalStalkMapLift, StalkLinearMapLocalLiftFinitePresentation,
   FiniteLocallyFreeStalkHomLift, and FiniteFreeReverseComponentsLift: these provide
   related single-map or finite-free results in different stalk/restriction APIs;
   the open-slice comparison and finite-family transport remain necessary work.
   Closing the geometric hole is not a few-minute application of those interfaces.
4. The proof performs the entire finite-support assembly rather than merely
   applying a restatement. Reviewed imports and the unit's realized fields: this
   node is below the unit level and no unit step is bypassed. The old internal-Hom
   proof dependency is removed from the item's direct route and remains in the
   geometric node's plan, as listed above. No original module is globally pruned.
5. Checked both node statements against Lean, the union of proof-step uses against
   proof_deps, and the proof/proof_origin against the actual reduction. The new
   node has the source, searches, creation, blueprint, chapter, unit, and Lean
   records required by the brief. Verdict: valid decomposition, one hole closed
   and one strictly simpler hole added, net zero.

Second-reading change: replaced the new module's unnecessarily broad public import
of PerfectComplex with Mathlib.Algebra.Category.ModuleCat.Sheaf.Free. Removing it
without that replacement fails on SheafOfModules.free; the narrower import compiles.
No proof or signature repair was needed. Added this independent review and the
additional search evidence in searches.jsonl.
