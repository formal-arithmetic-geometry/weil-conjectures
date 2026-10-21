## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.Scheme.Modules.affineRealizationRawEvaluation_bijective`
with the composite of three bijections. The cohomology functor sends the canonical
coefficient restriction isomorphism to an isomorphism; `sheafHDerivedEquiv.symm`
is bijective; and `isIso_rawRestrictedCohomologyComparison` supplies bijectivity
of the actual raw comparison. This is precisely the existing declaration's
natural-language proof. All signatures, definitions, attributes, options and imports
are unchanged. No dependency module is modified.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.Modules.affineRealizationRawEvaluation_bijective`
(node `def-weil-pbc-coherent-higher-image-classes`).

Zero holes remain in the item; zero holes are added and zero statements are split off.
The proof uses the existing canonical comparisons and their recorded supporting
proofs; this does not claim that their transitive dependencies are already sorry-free.

## No longer needed

None. No import, declaration, module or node is pruned. The existing definition's
route and its canonical coefficient and cohomology transports are retained.

## Where the brief, the DAG or earlier work was wrong

None. The existing docstring supplies the entire argument; Mathlib's `Sheaf.functorH`,
`ConcreteCategory.bijective_of_isIso`, and composition of bijections implement it.

## Second reading by X6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
