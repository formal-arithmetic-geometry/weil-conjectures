## What changed

Proved `WeilConjectures.FrobeniusCoefficientTwists.existsUnique_completedToOrdinary`
in `lean/Sheaf/Paper/FrobeniusCoefficientTwistsCanonical.lean`.
The proof descends the specified strict augmentation through the localization of good
complexes, restricts to integral constructible objects, and inverts the resulting natural
isomorphism. It verifies the exact representative normalization and proves uniqueness by
naturality along a good representative. It does not choose an arbitrary comparison.

Added only proof imports: `import all Sheaf.Paper.IntegralOperationsWellDefined`, to use its
proved private good-complex localization theorem, and
`import Sheaf.Paper.SfIntegralConstructibleTriangulated`, for isomorphism invariance of the
constructibility predicate. Both import directions were checked. Two local elaboration
options allow the existing definitionally equal coefficient and derived-category presentations.
All declaration signatures, definition bodies, existing docstrings and public imports stay
unchanged. No consumer adaptation or definition change is needed.

Updated the owning node's proof, proof dependencies and proof origin to record the descent
argument and the original obligations it still uses. No new node or Lean module is added.

The final proof compiled in 20.6 seconds. Its tactic-style warning was removed before
submission; the delivery gate performs the final clean compilation and axiom checks.

## Proved and sorry left

Closed 1 of the original 7 holes; added 0 holes; split off 0 theorems.
The closed declaration is
`WeilConjectures.FrobeniusCoefficientTwists.existsUnique_completedToOrdinary`.
This is a partial proof delivery, not a decomposition into new holes.

Six original holes remain, all in namespace `WeilConjectures.FrobeniusCoefficientTwists`
and all attached to node `def-weil-frobenius-coefficient-twists`:

- `existsUnique_positiveLineMaps`: root-normalized completed tensor-power comparisons.
- `existsUnique_signedLineMaps`: completed internal-Hom transport and evaluation uniqueness.
- `existsUnique_finitePositiveLineMaps`: normalized finite scalar/root tensor comparisons.
- `existsUnique_finiteSignedLineMaps`: finite internal-Hom transport and evaluation uniqueness.
- `existsUnique_pullbackAugmentation`: quotient-unit insertion, strict transition compatibility,
  the zero-second-component mapping-cocone lift, naturality and uniqueness.
- `pullbackAugmentation_isIso`: identify that particular augmentation with completeness under
  isomorphism-site reindexing, proving invertibility on complete good inputs.

These retain their original sources and proofs in words. The new descent proof uses the last
two named obligations as intended by stage 3; it introduces no additional assumption or hole.
The proof covers arbitrary schemes and every scheme isomorphism, including the empty scheme.

## No longer needed

No import, node or module is pruned. All existing public imports are retained for the published
coefficient constructions and the remaining obligations. The descent proof uses existing good
localization and constructibility invariance directly: no new resolution-independence theorem,
new good-representative existence statement or new comparison-existence lemma is needed.
The tensor/Hom and finite site-descent dependencies remain needed by the unresolved line maps.

## Where the brief, the DAG or earlier work was wrong

The owning node is a definition with originally empty proof and proof_deps, so it supplies no
numbered proof plan for this obligation. The existing theorem docstring specifies precisely the
localization descent implemented here. The unit's realized statement and steps are empty; no
unit route is bypassed.

The broader signed-line comparison theorem requires local freeness, while this item's sheaf
map declarations assume only a scheme isomorphism. Similarly, the finite site-descent and
integral twist inverse-image theorems require prime invertibility absent from these declarations.
They cannot simply be applied to discharge the unrestricted normalized sheaf-map obligations.
No false statement or definition defect was established, and no statement was weakened.

## Second reading by X9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
