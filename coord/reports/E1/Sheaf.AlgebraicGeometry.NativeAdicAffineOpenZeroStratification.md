## What changed

Proved `AlgebraicGeometry.ProEtale.affine_open_zero_stratification` in
`Sheaf.AlgebraicGeometry.NativeAdicAffineOpenZeroStratification`, preserving its complete
signature, universes, hypotheses and conclusions. Added two proved private helpers:
`finite_stratification_of_stratified` enumerates a native finite lisse stratification by
`Fin n`, and `open_zero_chart` constructs the chart comparison, complement vanishing and
glued stratification. The proof uses the already proved native constructible pullback,
qcqs stratification and `IsAdicStratifiedLisseSheaf.of_isCompl` declarations.

The square comparison is the actual `adicUpperStarCompIso` followed by the pullback of the
given isomorphism. Complement vanishing is derived pointwise using
`Scheme.Pullback.exists_preimage_pullback` and the stated `hzero`, then transported with
`adicUpperStarComp`. Constructibility on X follows by choosing affine neighbourhoods.
No definitions, public signatures or public imports changed. The node's proof and proof
dependencies now describe this implementation.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.affine_open_zero_stratification`
(node `lem-sf-native-adic-affine-open-zero-stratification`).
Added 0 holes; split off 0 statements. No sorry remains in the delivered Lean module.
Both private helpers are fully proved. Compilation is through `lcompile.py`; the delivery
preflight checks the axioms of all declarations.

## No longer needed

Removed these unused private proof imports:

- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`: the concrete Mathlib
  `vanishingIdeal` subscheme and its range lemmas construct the needed complement directly;
  the stronger uniqueness and ideal-characterization theorem is unnecessary here.
- `WeilConjectures.ConstructibleSheaf.Pullback`: native
  `IsAdicConstructibleSheaf.upperStar` already proves the needed constructible pullback.

Accordingly, the direct proof dependencies
`lem-weil-pbc-reduced-induced-closed-subscheme`,
`lemma-constructible-pullback-stratification`, and
`lem-weil-pbc-constructible-open-restriction` are unnecessary for this item.
`lem-weil-pbc-quasi-separated-affine-cover-criterion` is also unnecessary: the existing
`quasiSeparatedSpace_of_quasiSeparated` API handles the open projection into affine V.
The native constructible-pullback node replaces the manual pullback-stratification route.
No module is withdrawn, and no claim is made that these modules are globally unreachable.

## Where the brief, the DAG or earlier work was wrong

No statement discrepancy was found. The original seven-step plan can be implemented more
briefly using existing proved native sheaf APIs and Mathlib's explicit closed-subscheme
construction. The reducedness assumption on the supplied complement is retained, although
the chart helper proves the required conclusions for any closed complement with the exact
range. No separation or Noetherian hypothesis has been introduced. The finite enumeration
uses no nonemptiness hypothesis, and the zero restriction uses `IsAdicLisseSheaf.of_isZero`,
so empty charts, empty open/complement, and M = 0 require no exceptions.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
