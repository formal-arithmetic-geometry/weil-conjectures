## What changed

Replaced the proof of
`AlgebraicGeometry.Scheme.proEtaleConstantRingCompositeCoefficients_eq`.
The signatures, public imports, and both comparison constructions are unchanged.
A proved private helper computes the adjunct of a composite using the mate of the
canonical direct-image comparison. The main proof identifies the direct-image maps
by the sheafification Hom equivalence and naturality of `toSheafify`, takes adjuncts,
and applies `Iso.ext`.

The calculation reuses the argument of the already proved private lemmas
`adjunct_comp_comparison` and `proEtaleConstantComparison_comp` in
`Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`; those private declarations
cannot be applied from this module. No finite-ring hypothesis is used. Naturality
also covers empty schemes, identity arrows, and the zero ring.

## Proved and sorry left

Closed 1 of 1 existing holes:
`AlgebraicGeometry.Scheme.proEtaleConstantRingCompositeCoefficients_eq`
(node `pur713-def-pullback-comparison`). Added 0 holes; split off 0 statements.
No `sorry` remains in the delivered module. The private adjunction helper is proved.

## No longer needed

None. All four original public imports remain necessary to the existing signatures
or construction bodies. No new imports, dependency nodes, or modules are needed.
The existing node has no proof dependencies to prune, and the proof follows its
constant-section/sheafification argument unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The library already contains the general
constant-coefficient composition calculation as a private proved lemma in
`ProfiniteCoefficientInverseImage`, rather than an externally usable declaration.
The finite-only theorem in `ProEtaleConstantRingComposition` is unnecessary here;
its different inverse-image-comparison presentation is not imported.

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
