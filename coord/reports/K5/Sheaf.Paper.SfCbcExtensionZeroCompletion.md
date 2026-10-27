## What changed

Proved `AlgebraicGeometry.Scheme.sfCbcReducedCompletionUnit_isIso` using
`CategoryTheory.AdicSites.reductionCompletionUnit_isIso` on the AsSmall model.
Noetherianity transfers to the lifted coefficient ring. Counit naturality and the
triangle identity identify the transported completion unit with the model unit
followed by an isomorphism, so its strict reduction is invertible. A private
generic lemma assembles this into an invertible natural transformation;
whiskering with ordinary extension gives the stated reduced unit.

Proved `AlgebraicGeometry.Scheme.sfCbcFiniteCompletedHom_naturality` for arbitrary
derived morphisms and independently chosen K-flat models. A proved private helper
establishes tensor-comparison naturality through the scalar Hom equivalence.
Another records that the reduced completion unit followed by the completed finite
map is the tensor comparison. The existing inverse theorem makes that reduced
unit invertible; cancellation, completion-unit naturality, and functoriality of
reduction then give the desired square. No mathematical definition or public signature changes.

For compilation, five public data APIs name the existing standard derived
factorization isomorphisms with the exact endpoints used by the model and
extension functors: `sfCbcModelDerivedFactors`, `sfCbcModelExtensionFactors`,
`sfCbcTowerExtensionFactors`, `sfCbcEvaluateFactors`, and
`sfCbcFiniteModelFactors`. The normalization predicate and finite evaluation
use these isomorphisms. The normalization relation is represented with `HEq`
between the same composites; `heq_iff_eq` recovers the old equation because
their types are definitionally equal. The complex comparison uses Mathlib's canonical
composition comparison to give the termwise endpoints explicitly. Its
identity comparison on the target represents the same ordinary chain map.
Unfolding the APIs recovers their original values;
there is no new choice or mathematical condition. See
`coord/changes/K5-sf-cbc-derived-factorizations.md`.

A proved private equation exposes application of the scalar Hom equivalence.
Local irreducibility keeps its choice construction and derived comparison
isomorphisms from expanding repeatedly. Existing completion-adjoint proofs use
this equation explicitly. Generic proved private lemmas handle equivalence
additivity, exactness of termwise extension, the transported unit, and the inverse
formula without expanding the large geometric constructions. The private
invertibility proof now factors the
projection adjunct as reduction of the realization isomorphism followed by the
existing completion-reduction isomorphism. These settings are local to this file.
The elaborator respects definition transparency; no timing limit is changed.

Updated the existing node proof to record these arguments and the shorter
strict-unit dependency. There are no new nodes, statements with holes, or source
library changes.

## Proved and sorry left

Closed 2 of the original 13 holes:

- `AlgebraicGeometry.Scheme.sfCbcReducedCompletionUnit_isIso`.
- `AlgebraicGeometry.Scheme.sfCbcFiniteCompletedHom_naturality`.

Added zero holes. The following 11 named obligations remain unchanged, all in
`Sheaf.Paper.SfCbcExtensionZeroCompletion` and the existing node
`lem-sf-cbc-extension-zero-completion` (names below have namespace
`AlgebraicGeometry.Scheme`):

- `sfCbcExtensionModel_existsUnique`.
- `sfCbcOrdinaryTensorComparison_existsUnique`.
- `sfCbcTensorComparison_existsUnique`.
- `sfCbcRestrictExtensionIso_existsUnique`.
- `sfCbcFiniteTensorHom_isIso`.
- `sfCbcCompletionModelIso_existsUnique`.
- `sfCbcFiniteUnderlyingHom_transition`.
- `sfCbcModelComplex_kflat`.
- `sfCbcFiniteModelIso_existsUnique`.
- `sfCbcCompletedReductionIso_evaluation`.
- `sfCbcRealizationExtensionIso_existsUnique`.

## No longer needed

The node no longer needs `lem-sf-cbc-completed-pullback-unit-tower` for the strict
reduced-unit assertion. Its specialized pullback machinery is replaced here by
the already proved generic `lem-sf-cbc-small-site-reduced-unit`; the lifted model
requires only Noetherianity. The old node and its module are retained for other
consumers. No existing Lean import was removed, no module was withdrawn, and the
remaining planned dependencies are retained for the unchanged obligations.

The finite naturality proof needs no separate theorem about naturality of chosen
K-flat representatives or completion-model isomorphisms: the scalar adjunction,
the previously proved inverse calculation, and naturality of the specified
completion unit suffice.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The DAG's specialized
completed-pullback route for the strict reduced unit was unnecessary given the
existing generic theorem. The final target and its unit route are preserved.

Process incident: an early edit command used the shared working directory; its
replacements matched nothing and it rewrote the item with identical bytes. No
shared source content changed. All subsequent edits explicitly used the sandbox
working directory.

Edge cases: neither new proof uses nonemptiness of an open immersion, a nonzero
coefficient ring, boundedness, or completeness of the input. The equivalence
transport and categorical cancellation apply equally to identity and empty opens
and zero complexes. The naturality argument retains arbitrary independent models.

## Second reading by K5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
