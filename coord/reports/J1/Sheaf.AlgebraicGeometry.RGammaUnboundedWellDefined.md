## What changed

Proved `AlgebraicGeometry.Etale.rgamma_unbounded_well_defined` in
`Sheaf.AlgebraicGeometry.RGammaUnboundedWellDefined`, with its existing signature,
public imports and docstring unchanged. The proof implements all four DAG steps:
comparisons induce invertible derived maps; the Mathlib K-injective quasi-isomorphism
criterion makes them homotopy equivalences; additive global sections preserve these;
and the K-injective Hom bijection supplies existence and uniqueness up to homotopy
for the comparisons between different representatives.

Three fully proved private helpers handle elementary passage between the homotopy
quotient and localization, and preservation of invertibility after applying an
additive functor termwise. No new mathematical statement or dependency is needed.
The proof uses the existing private import
`Mathlib.Algebra.Homology.DerivedCategory.KInjective`.

Validation: the complete module compiled without errors or warnings through
`lcompile.py` in 4.5 seconds. The proof applies to arbitrary complexes, including
zero and unbounded complexes, and uses no exactness of global sections. In the
third clause, cancellation uses precisely the isomorphisms given by `e`, `e'`
and the quasi-isomorphisms `s`, `s'`.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.rgamma_unbounded_well_defined`
(node `lem-kun-rgamma-unbounded-well-defined`).

Zero holes remain in the item. Zero holes added. Zero statements split off.
All three private helpers are completely proved.

## No longer needed

Removed the redundant private import
`WeilConjectures.AlgebraicGeometry.DerivedCategories`, already available through
`Sheaf.AlgebraicGeometry.KInjectiveResolutions`.

No DAG dependency, node or module is pruned: the proof follows the existing route
and uses all the declared proof dependencies. In particular the existing right
derived global sections public import is retained. No resolution-existence theorem
is needed, as the resolutions are supplied as hypotheses; the DAG already omitted
that dependency.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was required. The Mathlib leaf
`lem-weil-pbc-kinjective-hom-derived` already includes
`CochainComplex.IsKInjective.quasiIso_iff`, so the inverse-comparison argument in
step 2 is reused directly from Mathlib. The existing node and unit route are
unchanged.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
