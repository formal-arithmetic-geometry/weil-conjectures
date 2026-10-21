## What changed

Proved the integral and finite signed twist comparisons by transporting the
internal Hom comparison through the positive-power and coefficient-unit maps.
The local evaluation formula determines each negative comparison uniquely.

Proved the completed-to-ordinary comparison by descending the strict augmentation
through the localization of good complexes, restricting to constructible objects,
and inverting its components. The proof checks the prescribed representative
formula and proves uniqueness by essential surjectivity.

Added only private proof imports and proved private helpers. Every existing public
signature, definition body and public import is unchanged. Recorded these proof
routes in the existing DAG node. The complete module compiled successfully in
36.2 seconds; delivery runs the independent preflight again.

## Proved and sorry left

Closed three of the seven original holes:

- `WeilConjectures.FrobeniusCoefficientTwists.existsUnique_signedLineMaps`.
- `WeilConjectures.FrobeniusCoefficientTwists.existsUnique_finiteSignedLineMaps`.
- `WeilConjectures.FrobeniusCoefficientTwists.existsUnique_completedToOrdinary`.

Four original holes remain, all owned by node
`def-weil-frobenius-coefficient-twists`:

- `WeilConjectures.FrobeniusCoefficientTwists.existsUnique_positiveLineMaps`.
- `WeilConjectures.FrobeniusCoefficientTwists.existsUnique_finitePositiveLineMaps`.
- `WeilConjectures.FrobeniusCoefficientTwists.existsUnique_pullbackAugmentation`.
- `WeilConjectures.FrobeniusCoefficientTwists.pullbackAugmentation_isIso`.

No holes added and no split-off statements. The signed proofs use the existing
positive-map declarations. Descent uses the existing augmentation and its
invertibility declaration, as intended for stage 3.

## No longer needed

None. No public imports, nodes or modules withdrawn. All original imports are
retained for the published definitions and statements. No source-library
declaration is removed or weakened. The new proof imports are private.
The node originally had no proof dependencies to prune.

## Where the brief, the DAG or earlier work was wrong

The item's node had no numbered proof steps or proof dependencies. Its declaration
docstrings supply the arguments now recorded for the three completed proofs.

The existing general Tate-line inverse-image and termwise derived-pullback theorems
assume invertibility of ell on the schemes. The positive-power and completeness
statements here quantify over all scheme isomorphisms, so applying those theorems
directly would require an additional hypothesis. No hypothesis was added.

An attempted augmentation construction used the finite scalar-reduction units,
the finite inverse-image units and the restriction/direct-image comparison,
followed by a product and a mapping-cocone lift with zero second coordinate.
Its section and naturality checks remain unfinished; no part of that draft or
any new unproved intermediate statement is included in this delivery.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
