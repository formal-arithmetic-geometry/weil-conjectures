## What changed

Replaced the sorry proof of
`CategoryTheory.CondensedDerivedRestriction.internalBarCharacterRoofCup` by a reduction
that chooses the universal signs from `internalInflationGradedCup`, applies degree-one
character normalization, proves the ordered-roof cancellation identity, and performs the
ordered-cup induction. Seven existing definitions and the theorem signature are verbatim unchanged.
The eighth definition, `characterRoof`, has the same displayed composite packaged
in a generic irreducible wrapper with proved equations; its signature is unchanged.
The unchanged `orderedShiftedArrows` definition is moved to `InternalShiftedRoof`
and publicly reexported by the item.

The generic module `Sheaf.CategoryTheory.InternalShiftedRoof` and its private
categorical helpers prove that shifted conjugation preserves composition
and the zero-shift identity, and express the localized roof as conjugation of
`ShiftedHom.map`. Mathlib's `ShiftedHom.map_comp` then gives the ordered-roof identity
for arbitrary lifts, without character conditions or projectivity.

Added the proof import `Sheaf.CategoryTheory.InternalBarCharacterLiftNormalization`
and a new module of that name for the unresolved degree-one extension/adjunction
normalization (the original plan's steps 1–3). Added the proof import
`Mathlib.Tactic.Ring` for the scalar recursion calculation, and the public import
`Sheaf.CategoryTheory.InternalShiftedRoof` for the wrapper used in the roof definition.
The new normalization lemma states the
actual generalized-generator equation and localized roof explicitly; it does not
assume any conclusion about ordered roofs, products, or the universal signs.

The three modules compiled through `lcompile.py --all`. The unused profinite
section assumptions on the private bilinearity lemma were removed before delivery;
`deliver3.py` checks the final files again with the declaration and axiom probes.

## Proved and sorry left

Closed the original textual hole in
`CategoryTheory.CondensedDerivedRestriction.internalBarCharacterRoofCup`
(node `lem-sfb-internal-bar-character-roof-cup`). One original hole, one closed.
The ordered-roof cancellation, empty family case, bilinearity calculation and
finite ordered-cup induction have complete Lean proofs.

Added one hole:
`CategoryTheory.CondensedDerivedRestriction.internalBarCharacterLiftNormalization`
(node `lem-sfb-internal-bar-character-lift-normalization`). Its whole proof is
`:= by sorry`; its docstring gives the extension-generator construction, the
canonical negative boundary comparison by the explicit cone argument, identification
of the prescribed augmentation,
and the shifted-adjunction normalization. The cone proof is carried out directly in
the specified coefficient localization, so no universe-changing bar model is chosen. There are no remaining holes in the item
module, no holes in definitions, and no other new holes. This is a decomposition,
with net hole change zero, not a complete proof of the mathematical normalization.
Existing imported postponed results are used as permitted by stage 3.

## No longer needed

No existing public import or library module was removed, and no node is withdrawn.
The original plan's direct proof dependencies
`lem-sfb-condensed-derived-restriction-calculus`,
`lem-sfb-condensed-internal-bar-resolution`,
`lem-sfb-internal-bar-roof-adjunction`, and
`def-sfb-condensed-unipotent-class` now support the degree-one normalization lemma
rather than separate steps of the parent's proof; they remain needed transitively
and for the existing definitions. The parent's new direct proof dependencies are
that normalization lemma, `lem-sfb-internal-inflation-graded-cup`, and
`def-weil-abstract-derived-category`, together with the wrapper/API node
`def-sfb-localized-shifted-roof`.

The proof does not need `Sheaf.CategoryTheory.InternalBarCharacterLifts`: existence
and uniqueness of prescribed explicit chain lifts are unnecessary when the theorem
already quantifies over supplied lifts. This module was not an original dependency
and is not claimed pruned from the project's closure. No modules are claimed pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed. Profiling exposed slow repeated kernel checking
of the expanded concrete roof. The generic wrapper contains precisely the original
composition; only this new wrapper is irreducible, and its proved composition and
zero-degree API replaces repeated expansions. The finite-roof induction is also
proved in that generic module and specialized in the item; its original ordering
recursion is moved verbatim and publicly reexported. Direct-import searches and downstream.py
found no existing external importer or declaration user to adapt.
The original DAG describes the character
extension computation and adjunction normalization but its recorded Lean dependencies
do not directly state that combined degree-one specialization. That remaining argument
is now explicit as one genuine smaller statement. The current blueprint paragraph (3)
provides the open-direct-image application, not a textbook proof of this internal bar
normalization; the source remains the agent-formulated proof already recorded on the
item, and an exact external reference is still wanted.

The source unit's realized statement and steps were retained. The scalar induction
also treats the transition from q=0: its needed identity is t(0,1)=1, so the exceptional
T(1)=1 agrees with the uniform signed recursion. Zero ring, trivial character or group,
characteristic two, and the empty family introduce no additional hypotheses.

Mathlib searches used LeanFinder, Loogle, LeanSearch and grep. They found
`ShiftedHom.map_comp` for localization and standard single-boundary/cochain APIs,
but no internal condensed character-roof normalization. A repository search also
checked `InternalBarCharacterLifts` and `CondensedUnipotentBoundaryNaturality`; neither
states the remaining roof and shifted-adjunction comparison.

## New nodes

`lem-sfb-internal-bar-character-lift-normalization` is steps 1–3 of the original
argument, for a single degree-one lift. It uses the same coefficient and group
universes, the existing extension and positive character class, and the same
canonical localization and shift comparisons. Its statement is strictly smaller
than the item: all finite ordered roof and cup assertions, the universal sign family,
and their assembly have complete Lean proofs in the delivery.
The representation-only definition refactor is recorded in
`coord/changes/S1-internal-character-roof-wrapper.md`.

`def-sfb-localized-shifted-roof` packages the generic localized shifted roof for a
shift-compatible functor, an invertible localized augmentation, and a specified
endpoint isomorphism. The construction chooses no data. Its composition and zero-shift
identity equations and the finite ordered-composition theorem are completely proved
from Mathlib shift functoriality and inverse cancellation; this module adds zero holes. Its irreducible wrapper addresses the
profiled repeated expansion cost without changing the maps or mathematical meaning.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
