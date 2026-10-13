## What changed

Proved `AlgebraicGeometry.Scheme.CompletionGluingData.completedRingMap_kernel_local_torsion`
without changing its statement. The proof chooses finite maximal-ideal generators, puts
each associated principal open inside U, and uses Mathlib's
`Localization.awayMap_injective_iff` to obtain the individual annihilating powers.

Added the fully proved module
`Sheaf.AlgebraicGeometry.Morphisms.CompletedMatchingRingMapAwayOfPuncturedIso`.
Its theorem derives bijectivity of the localized completed comparison from
`IsIso D.puncturedMap`. This bridge does not require Noetherianity, that U be the
punctured spectrum, or finiteness of q. The proof transports the overlap pullback,
pastes restriction squares, compares it with the Spec of the ring pushout, and
then uses `SpecMapRestrictBasicOpenIso` and `isIso_SpecMap_iff`.
Every private helper is proved. No object is chosen from an unproved existence theorem.

The item's two added proof imports are the new bridge and the existing
`PuncturedCompletionMatchingPuncturedIso`. Updated its DAG proof and proof dependencies.
Existing public imports, declaration signatures, and definitions are unchanged.

Both delivered modules compile without warnings through lcompile.py. A separate
axiom check showed only propext, Classical.choice and Quot.sound for the new bridge.
The assigned theorem still has transitive sorryAx from the already existing punctured
comparison route; this is not a claim that the entire import closure is sorry-free.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.CompletionGluingData.completedRingMap_kernel_local_torsion`
(node `lem-sbc-completed-matching-ring-map-kernel-local-torsion`).

Also proved the new theorem
`AlgebraicGeometry.Scheme.CompletionGluingData.completedRingMap_away_bijective_of_puncturedMap_isIso`
(node `lem-sbc-completed-matching-ring-map-away-of-punctured-iso`).
No sorry remains in either delivered module; no hole was added or split off.
The existing external theorem
`AlgebraicGeometry.Scheme.CompletionGluingData.exists_puncturedMap_basicOpen_appTop_ringEquiv`
remains sorry in `PuncturedCompletionMatchingAffineSectionsComparison`; it is reached
through the existing punctured comparison theorem, and is not modified by this delivery.

## No longer needed

No existing import was removed. A trial import of Mathlib.RingTheory.Noetherian.Basic
was removed after verifying that the existing public imports already expose the
finite-generation facts. Both new proof imports are used.

The assigned node no longer directly depends on
`lem-weil-pbc-formal-glueing-H0-localization` or its module
`Sheaf.RingTheory.FormalGlueingH0Localization`: it reuses the already stated punctured
comparison. The H0 theorem remains relevant to the source proof of that punctured
comparison and elsewhere in the project; no global pruning of its module is claimed.
The direct proof dependencies on the matching-sections and finite-morphism definition
nodes are also unnecessary here (they remain statement dependencies or are used by
the punctured comparison). No blueprint unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned abstract H0 theorem has a formal-gluing-data/module signature, not a
signature for D.matchingRing. Rather than reconstruct that interface again, this
proof uses the existing punctured comparison and proves the remaining geometric
base-change bridge directly. This is a shorter implementation of the same
principal-open localization argument, not a correction of either statement.

The blueprint ancestor tool returns None for this item because its existing created.item
is a module name. The new node's ancestor and via chain were instead traced explicitly
through the kernel-torsion and injectivity nodes to
`sbc-thm-spreading-finite-etale-galois`. Searches found no duplicate bridge.
The local literature/stacks-project/more-algebra.tex file is absent on this machine;
the cited source was read at https://stacks.math.columbia.edu/tag/05ER, with its
05EQ and 05EP references. No source or tool file was modified.

Edge cases: t=0 gives a vacuous generator assertion; f=0 or any nilpotent f gives
empty principal opens and zero localization rings. Pullback transport and the
localization criterion handle these cases without nonzero assumptions. The bridge
also works for arbitrary U under the stated containment hypothesis, including empty U.

## New nodes

`lem-sbc-completed-matching-ring-map-away-of-punctured-iso` is the fully proved
principal-open base-change bridge. Its source is the localized-comparison paragraph
of Stacks 05ER, applied to the 0BLH overlap. The statement records all data, the
punctured isomorphism assumption, and exactly the canonical awayMap. LeanFinder,
Loogle, Mathlib grep and local library searches supplied generic tools but no
duplicate theorem; LeanSearch returned an internal server error and is recorded
as unavailable. There are no statement/interface changes or change records.

## Second reading by G4

1. Compared both delivered modules with the repository versions. The existing target
   declaration and all definitions are byte-for-byte unchanged; only the target proof,
   its proof imports, and the new bridge module were added.
2. Compiled both modules with `lcompile.py`. The target has no local `sorry`; the new
   bridge has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`.
   Axiom inspection of the bridge gives only `propext`, `Classical.choice`, and
   `Quot.sound`; the target's transitive `sorryAx` comes from the pre-existing punctured
   comparison theorem.
3. Checked the bridge statement and edge cases (empty principal opens, nilpotent or
   zero `f`, and empty `U`). It is strictly the localized away-map bijectivity needed by
   the target and does not restate the target or weaken any existing statement. Searches
   found no duplicate declaration in Mathlib or the library.
4. Read the proof top-down. It uses the existing punctured comparison, finite
   generation, pullback pasting, and `SpecMapRestrictBasicOpenIso`; no shorter available
   theorem was found. The unit route remains intact, and the DAG proof/proof-dependency
   records match the imports and declarations actually used.
5. Verified that the new node contains its source, proof steps, searches, Lean record,
   and blueprint ancestry, and that the target node records the closed hole and the new
   bridge dependency.

Changed only this report during second reading; no proof or statement repair was needed.
