## What changed

Replaced the proof hole in `AlgebraicGeometry.Etale.openImmersion_generalField_uniformBound`
with the finite-type cohomological-dimension argument and existing affine-etale higher-image
vanishing criterion. The statement is unchanged. Added proved private helpers for empty-scheme
cohomology, monotonicity of the finite-type bound with a dimension upper bound, and the
module/abelian higher-image comparison. All helper data are explicit compositions of existing
proved isomorphisms. Updated the item's DAG proof and dependencies to follow this argument.

The geometry uses the source specialization-chain dimension inequality for etale maps.
Finite-type-over-Noetherian and quasi-compactness instances establish the affine-test finite-type
clauses. Primary torsion is transferred to local torsion through geometric stalks. The positive
integer degrees are converted to natural degrees before applying the torsion bound. Finite
coefficient rings suffice for module torsion; the original prime-power and invertibility
hypotheses remain verbatim. All-degree empty-open vanishing is proved separately.

Validation: `lcompile.py` compiled the final module cleanly in 20.6 seconds (exit 0).
Earlier compile-service no-answer and missing-artifact failures cleared; the returned Lean
instance diagnostics were repaired. The import-direction checks for the new proof imports
pass. Edge cases checked in the argument: empty U or test pullback, dimension zero, c = 0,
zero coefficient ring, exponent zero (which forces the coefficient ring zero), and all integer
degrees in the empty clauses.

## Proved and sorry left

The only original hole is
`AlgebraicGeometry.Etale.openImmersion_generalField_uniformBound`
(node `lem-sf-open-general-field-uniform-bound`). Its complete proof compiles without sorry.
There are zero remaining sorry terms in the item and zero added holes or split-off statements.
The three private helpers contain complete proofs/constructions. The final single-file compile succeeded with no warnings.

## No longer needed

Removed proof imports:

- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: the finite-type instances suffice.
- `Mathlib.AlgebraicGeometry.Sites.AffineEtale`: the existing affine-test criterion contains
  the affine-cover argument.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: already exposed through the statement's
  cohomological-dimension import.
- `WeilConjectures.AlgebraicGeometry.Dimension` and
  `WeilConjectures.RingTheory.Etale.LocalDimension`: use the existing etale specialization-chain
  dimension inequality instead of local ring dimensions.
- `WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal` and
  `WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImagePresheaf`: use the existing
  `Sheaf.AlgebraicGeometry.Sites.HigherDirectImageAffineEtaleBound` criterion.

The item no longer directly requires nodes `def-sbc-locally-finite-presentation`,
`def-weil-open-immersion`, `lem-pc-scheme-dimension-local-rings`,
`lem-sc-etale-local-dimension`, `lem-weil-pbc-affine-etale-essentially-small-cover`,
`lem-weil-pbc-site-sheafification-sections-local`, or `sbc-lem-higher-direct-image-presheaf`.
The five corresponding obsolete tool-use entries were removed. The open immersion definition
remains part of the unchanged statement interface. No module is withdrawn: the replacement
criterion may itself use some of these results, and other library consumers may need them.
Added existing nodes `lem-kun-dimension-finite-type`,
`lem-sfb-higher-direct-image-affine-etale-bound`, and
`def-kun-topological-krull-dimension` to the actual proof dependencies.

## Where the brief, the DAG or earlier work was wrong

No statement repair was needed. The planned local-ring dimension comparison and manual
sheafification proof are unnecessary because the source dimension inequality and existing
affine-etale criterion already give those steps. The finite coefficient ring alone establishes
torsion of every module sheaf; no ring annihilator calculation is needed for this part.
The localization unit's route is preserved. No source-library declaration, signature, attribute,
public import, or non-theorem body is changed.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
