## What changed

Kept the statement and public imports of
`AlgebraicGeometry.exists_derivedProjectionMate_openRestriction_comparison` unchanged.
Its proof identifies the supplied source and morphism using hZ and hg, constructs N
and E as actual restrictions, proves their quasi-coherence with the existing restriction
criterion, and constructs source/target comparison isomorphisms. The proved private
`mate_square` combines Hom-equivalence compatibility and the tensor/counit equation
using adjunction naturality; `Arrow.isoMk` packages the resulting commuting square.

Added `DerivedOpenRestrictionLocalization`, proving that exact derived restriction is
a localization at the maps it makes invertible. The proof derives the existing exact
extension-by-zero adjunction, uses the existing extension/restriction isomorphism,
and applies Mathlib's `fullyFaithfulLOfCompIsoId` and `isLocalization'`. This works
with independent localization universes.

Added `OpenRestrictionAdjunctionHomDescent`, proving coherent descent of the supplied
adjunction from the localization theorem, the existing pullback/direct-image
restriction isomorphisms, and Mathlib's `Adjunction.localization`. Its private
`localization_hom` proves compatibility for every morphism by the localized unit
formula and naturality. Added `OpenRestrictionTensorCounitDescent` for the remaining
coherence step before taking an adjunction transpose. All added imports of the item's
module are proof-only; no existing signature or definition changed.

## Proved and sorry left

Validation status: all four delivered modules compile locally. The main module compiles
with its complete reduction and no warnings in 20 seconds. Local irreducibility of the
fixed derived localization, tensor, pullback, restriction and homology constructions
prevents expensive unfolding during functor-type comparison. No definition or public
interface was changed, and the proof was not split to evade the compilation limit.
The tensor descent application is explicitly staged; the restriction criterion's
localization universes and the underived restriction lemma's site are explicit.
The required delivery dry run is the final validation step. No delivery was pushed.

Replaced the original hole in
`AlgebraicGeometry.exists_derivedProjectionMate_openRestriction_comparison`
(node `lem-pc-derived-projection-mate-open-restriction-comparison`). Its module has
no remaining sorry; its proof is a reduction from the named descent statements.

Also proved the new public declarations
`AlgebraicGeometry.schemeDerivedOpenRestriction_isLocalization`
(node `lem-pc-derived-open-restriction-is-localization`) and
`AlgebraicGeometry.exists_openRestriction_adjunction_hom_descent`
(node `lem-pc-open-restriction-adjunction-hom-descent`), and the private helpers
`mate_square` and `localization_hom`.

The sole added hole is
`AlgebraicGeometry.exists_openRestriction_tensor_counit_descent`
(node `lem-pc-open-restriction-tensor-counit-descent`, module
`Sheaf.AlgebraicGeometry.OpenRestrictionTensorCounitDescent`). Its proof is exactly
`by sorry`, with source and proof in words. It constructs the tensor comparison
and proves the equation for the input morphisms before transposition; it asserts
no comparison in the arrow category and mentions no quasi-coherent local objects.

This is a decomposition: one original hole closed, one new hole added, net zero.
The localization and adjunction-descent parts and the final mate calculation are
proved from named existing declarations; the tensor/counit coherence still needs work.

## No longer needed

No existing import was removed: the original public imports occur in the preserved
statement. No invertibility or qcqs projection-formula theorem is imported.

The former planned proof dependencies
`lem-pc-derived-open-localization-universe`
(`Sheaf.AlgebraicGeometry.DerivedOpenLocalization`) and
`lem-pc-open-derived-localization-adjunction`
(`Sheaf.AlgebraicGeometry.OpenDerivedLocalizationAdjunction`) are no longer needed
on this item's branch. The new localization proof works directly with the fixed
small localizations using extension by zero. Neither module occurs in the delivered
item's import closure (checked recursively from the sandbox and repository sources).
Their nodes remain in the repository for other users.

The remaining former dependencies are retained as statement dependencies or through
the new lemmas: the derived-category, pullback, direct-image, tensor and restriction
definitions, the quasi-coherence restriction criterion, the pullback/tensor restriction
comparison and the direct-image restriction comparison. Thus none of these is claimed
as globally pruned. The updated parent proof_deps records the actual immediate route.

## Where the brief, the DAG or earlier work was wrong

The existing DAG was a valid mathematical plan but did not state the coherent
Hom-equivalence descent or the tensor/counit equation required to carry it out.
Objectwise or unrelated natural isomorphisms alone do not identify projection mates.
The delivery makes those two steps explicit and proves the former.

The fully faithful derived extension-by-zero left adjoint gives a shorter localization
argument than constructing a derived open-direct-image right adjoint in a separately
chosen ambient-universe category. This change is below the unit level. The item's
unit `sk-thm-picard-duality` has no realized statement or proof step assigned to this
node; its route and record are unchanged.

The pullback restriction theorem uses `resLE`, while the target uses
`morphismRestrict`; `Scheme.Hom.resLE_eq_morphismRestrict` is needed explicitly.
The comparison data in CatCommSq must be bound with `let`, so its chosen isomorphisms
remain visible to Lean. Local small localization instances are also explicit in the
main proof. The earlier attempt's timeout was reproducible. Local irreducibility of
`HasDerivedCategory.ofIsGrothendieckAbelian`, `schemeDerivedTensorMonoidal`,
`derivedPullback`, `Functor.mapDerivedCategory`, and `DerivedCategory.homologyFunctor`
resolved it without changing their definitions. Compile-slot queueing can add minutes
to the printed elapsed time; the compiler itself remains subject to the 60-second
limit. The allowed compile tool was used throughout.

LeanSearch returned HTTP Internal Server Error for all three new-node searches;
they are recorded as unavailable. LeanFinder and source grep ran successfully.
The searches found generic localization/adjunction and underived restriction tools,
which were inspected and used, but no theorem with the new scheme-level statements.

## New nodes

`lem-pc-derived-open-restriction-is-localization` states the localization property
of derived open restriction with independent localization universes. It is proved
from the existing exact adjunction and extension/restriction comparison, and generic
Mathlib localization tools. Its module is `DerivedOpenRestrictionLocalization`.

`lem-pc-open-restriction-adjunction-hom-descent` is the tensor-independent descent
of an arbitrary supplied adjunction, including compatibility for every Hom-equivalence
input. It is proved using localization and the two existing functor comparisons.
Its module is `OpenRestrictionAdjunctionHomDescent`.

`lem-pc-open-restriction-tensor-counit-descent` is the remaining tensor/counit step,
with its equality before applying the local adjunction transpose. Its docstring and
node expand the source's locality argument. The equation is well-typed for arbitrary
objects, including zero objects and empty opens. No compactness, separation,
boundedness or quasi-coherence condition was added. Its module is
`OpenRestrictionTensorCounitDescent`. The change record is
`coord/changes/DerivedProjectionMateOpenRestrictionComparison-proof-scope.md`.
There are no forced adaptations.

## Second reading by F2

1. Compared the delivered main module with the repository version. The target
statement and its public imports are byte-for-byte unchanged; only proof-local
imports, attributes, helpers, and the proof body changed. The three new theorem
signatures are recorded verbatim in their node files.

2. Compiled all delivered modules with `lcompile.py` and checked the source for
forbidden declarations and `sorry`. The only remaining `sorry` is the complete
proof of `exists_openRestriction_tensor_counit_descent`, with a named node and
source-backed docstring. The axiom check allows the permitted base axioms and `sorryAx` from
this explicitly open theorem and the still-open imported library statements.

3. Read each split-off statement and tested its scope conceptually on empty opens,
zero objects, and arbitrary morphisms. The localization and Hom-descent statements
are strictly simpler than the target and independent of tensor; the tensor/counit
statement is the pre-transpose equation and does not restate the target. No matching
library theorem was found by source grep or the recorded searches.

4. The proof follows the stated unit route through derived restriction, pullback and
direct-image comparisons, with localization used below the unit level. The two
obsolete localization-adjunction modules are removed from the proof dependency
closure, as recorded above; the localization module
originally exposed Mathlib localization adjunction tools only used by its proof;
changed that import to proof-only. Its statement still compiles.

5. Checked the new node records against declarations, proof steps, sources, and
module paths. The unit and chapter records are unchanged, and the change record
documents the proof-local elaboration controls without changing any interface.

Changed during second reading: made the localization adjunction import proof-only.
Expanded the new tensor/counit docstring and node proof to use full faithfulness of
precomposition with the product localization, avoiding an unnecessary unstated
right-adjoint construction. No existing signature, definition, or proof was altered.
Independent searches used the queries `localization.*tensor|tensor.*localization|
homEquiv.*counit` and extension of bifunctor isomorphisms across localization.
Mathlib provides generic `Localization.lift₂NatIso`, but no scheme tensor/counit
descent theorem; constructing natural tensor restriction remains the open part.
