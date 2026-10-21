## What changed

Restored `lean/Sheaf/AlgebraicGeometry/StandardSingleFlatCounitLocalizationCompletion.lean`
from the exact quarantine archive named in `coord/rework.tsv`. Its theorem,
`AlgebraicGeometry.standardSingleFlatCounit_localization_completion`, already had
no holes. Its entire signature, universe, docstring, options and public import
are preserved. The proof names the existing localization homology result before
destructuring it, then retains the constructed stalk complex, its bound and
flatness, the universal scalar-extension pair and all comparison squares. Only
the additional equality identifying that complex with the presentation's stalk
complex is discarded. There is no new definition or arbitrary witness construction.

Updated the existing node
`lem-pc-standard-single-flat-counit-localization-completion` in `proof`,
`proof_deps` and `proof_origin` to describe this actual proof. Its Lean attachment,
mathematical statement and all statement dependencies stay intact. No new node,
statement correction, source-library edit or target change is introduced.

The archived theorem initially fails against the published homology artifact:
`Tactic generalize failed: result is not type correct`. Naming its premise
exposes `unknown constant ModuleCat.extendScalars_additive_sheaf`, the retired
additivity theorem. Broad proof imports do not fix that artifact and are not
retained. Recompiling the current, unchanged source of
`StandardSingleFlatCounitLocalizationHomology` in the sandbox resolves the
failure. The item then compiles in 9.5 seconds. A second set compiles the current
homology source in 23.6 seconds and the unchanged archived direct consumer,
`StandardSingleFlatCounitLocalization`, in 6.4 seconds. These dependency and
consumer copies are scratch checks only and are not delivered. The delivery
uses the current homology source; it must not be checked against its stale
compiled interface.

Separate `#print axioms` checks of the restored theorem and the unchanged
archived parent both report exactly `propext`, `Classical.choice` and `Quot.sound`.
They compile in 5.8 and 5.4 seconds respectively against the current homology
source. Thus this route has no transitive proof hole either.

The exact original public import and the sole original proof import are kept.
The import-direction check allows the homology dependency. All delivered Lean
lines are at most 100 characters. The live downstream query with
`--allow-missing` finds zero importers because the item and parent are
quarantined; the combined live/archive graph has one direct and 92 transitive
consumers. Their inventory and unchanged meanings are recorded in
`coord/changes/D3-standard-single-flat-counit-localization-completion-restoration.md`.
No consumer is adapted. Quarantine archives remain untouched.

The dependency declarations and the Picard-coherence unit were read. The Stacks
arguments were checked in `perfect.tex`, lemma-single-complex-base-change
(0DJ9), and `cohomology.tex`, lemma-check-K-flat-stalks (06YB) and
lemma-derived-pullback-composition (0D5S). The unit's route is preserved.
LeanFinder supplied flat-stalk infrastructure but no shorter matching theorem;
Loogle did not recognize the queried derived-functor identifier; the logged
Mathlib grep had no matching stalk/counit theorem. The library's existing
localization homology theorem gives the required result directly.

## Proved and sorry left

Zero original holes, zero remaining holes. The complete proof of
`AlgebraicGeometry.standardSingleFlatCounit_localization_completion`, node
`lem-pc-standard-single-flat-counit-localization-completion`, is restored.
Holes closed: none (0 of 0). Holes added: none. Split off: none.
Every `sorry` left in delivered Lean: none. This is a zero-hole restoration,
not a new hole closure or a decomposition.

## No longer needed

No Lean import is removed and no module is withdrawn. Remove the stale direct
proof-dependency edges to
`lem-pc-standard-single-flat-counit-localization-data` and
`lem-pc-standard-single-flat-counit-localization-pair` from this node's plan.
The data theorem merely supplies some bounded flat complex; that assertion does
not identify the complex required by the comparison. The retained homology
theorem supplies the actual complex together with all remaining data. The pair
theorem remains used inside that homology theorem, so it is not pruned from the
transitive route. Both source modules remain intact; no whole-module pruning
or import-closure hole reduction is claimed. The homology dependency, the
parent's call to completion and the unit route remain needed.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an item with holes. This assignment instead
restores a quarantined module whose archived theorem has a complete proof.
Its absence is not a withdrawal request. The old DAG plan did not match its
Lean body: it separately selected a complex and a pair, although the homology
theorem already selects the complex from the same local presentation and
supplies its pair and comparisons. The updated plan records the existing
shorter argument without weakening any statement.

The first compiled interface encountered still referred to the removed
`ModuleCat.extendScalars_additive_sheaf`. Current source re-elaboration, rather
than adding imports or recreating the retired theorem, resolves it. The
unchanged archived parent compiles against the restored item and the current
homology source. No mathematical defect or new unresolved step was found.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
