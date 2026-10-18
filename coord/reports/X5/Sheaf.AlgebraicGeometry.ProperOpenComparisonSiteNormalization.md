## What changed

Proved `AlgebraicGeometry.ProEtale.properOpenComparison_site_normalization` without
changing its signature or any definition. The named pro-etale isomorphism already
contains precisely the required four factors. Unfolding its hom and the two comparison
names reduces the equality to cancellation of the first open-comparison inverse.
Updated the existing node's proof, proof dependencies and proof origin to this route.
The unit's statement and steps are unchanged.

The final sandbox module compiles cleanly through lcompile.py. No new module,
statement, definition, axiom, or postponed proof was introduced.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.properOpenComparison_site_normalization`
(node `lem-sf-proper-open-comparison-site-normalization`).

Item holes: 1 before, 0 after. Holes added: 0. Split-offs: 0.
`properOpenNormalizationCoefficientFinite` remains its existing proof.
Imported declarations may still depend on their existing postponed proofs; this
normalization proof does not claim to close those independent obligations.

## No longer needed

Removed all eleven private proof imports:

- `WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous`
- `Mathlib.CategoryTheory.Adjunction.Additive`
- `Mathlib.CategoryTheory.Adjunction.Triple`
- `WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`

All four public imports are retained for the statement and coefficient instance.
No whole library module is claimed unreachable from the targets.

The following formerly declared proof dependencies are no longer needed separately
by this normalization argument:

- `lem-weil-pbc-locally-noetherian-quasi-separated`
- `lem-weil-pbc-qcqs-morphism-permanence`
- `lem-cbc-proetale-extension-zero-comparison`
- `lem-weil-pbc-extension-by-zero-exact`
- `lem-weil-extension-by-zero-exact`
- `def-weil-pbc-proper-open-comparison`
- `lem-weil-pbc-proper-open-comparison-iso`

The existing pro-etale comparison construction already incorporates the required
open comparisons, exact derived descent, specified etale arrow and invertibility.
Properness supplies its hypotheses directly. These results may remain indirect
dependencies of that construction; no global pruning of their modules is asserted.

## Where the brief, the DAG or earlier work was wrong

The original plan repeated the construction of the derived comparisons and their
invertibility. Those were already implemented in `properOpenProEtaleIsoPlus`.
The normalization is its defining composite with the initial inverse cancelled.
There is no statement correction or source error. Searches through the prescribed
LeanFinder, Loogle and grep tools found the applicable abstract cancellation lemma;
reading the library construction established that it applies to this named map.

## Second reading by X5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
