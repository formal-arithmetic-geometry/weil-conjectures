## What changed

Filled the proof of
`AlgebraicGeometry.Scheme.quasiAffine_open_principal_comparison_cover`
in `Sheaf.AlgebraicGeometry.QuasiAffineOpenPrincipalComparisonCover`.
The statement and the existing Mathlib import remain unchanged.

The proof follows the five stated steps using their Mathlib realizations:
quasi-affineness supplies the canonical open immersion; naturality gives the square;
the distinguished-open basis covers the composite image; injectivity and basic-open
preimage formulas give the image containments; `IsAffineOpen.Spec_basicOpen` and
`preimage_of_isOpenImmersion` prove affineness; `isoOfRangeEq` constructs both
isomorphisms and proves their required compatibility equations. Pulling back the
basis cover proves coverage of U, without any quasi-compactness hypothesis on U.

The remote single-file compiler passed without errors or warnings (1.8 seconds).

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.quasiAffine_open_principal_comparison_cover`
(node `lem-a1-quasi-affine-open-principal-comparison-cover`).
No sorry remains in the item; no holes were added or split off.
Every ingredient comes from Mathlib.

## No longer needed

No imports removed and no nodes or modules pruned. The existing public Mathlib
import supplies all the planned ingredients. Affineness of distinguished opens
is used through Mathlib's proved `IsAffineOpen.Spec_basicOpen`, so there is no need
to reconstruct localization isomorphisms in this proof. There are no additional
Sheaf or WeilConjectures proof imports.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. The proof follows the existing node plan, using
Mathlib's open-immersion and affine-open APIs for its restriction arguments.
The statement is unchanged, including the absence of a quasi-compactness
hypothesis on U. No new nodes, definition repairs, or consumer adaptations.

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
