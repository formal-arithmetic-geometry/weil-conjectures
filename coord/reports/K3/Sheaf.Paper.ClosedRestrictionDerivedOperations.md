## What changed

Filled `AlgebraicGeometry.ProEtale.CondensedRing.closed_restriction_derived_operations`
in `Sheaf.Paper.ClosedRestrictionDerivedOperations`. The public statements and
existing definitions are unchanged. Private proved helpers assemble products,
signed-shift compatibility, bounded functorial section models and continuity on
normalized representatives.

Added private proof imports for the source modules
`DerivedDirectImageKInjectiveShiftComparisonAux`, `ProductsMapDerivedCategory`,
`TowerLimit`, `AdjunctionShift`, and `KInjectiveResolutionInjective`, plus
`Sheaf.AlgebraicGeometry.ProEtaleProductsExact`. They provide the existing signed
unit equation, generic product constructions, and degreewise injective resolution.
A local priority adjustment uses the existing shape-level colimit instance and
avoids repeated degreewise instance searches; it adds no public declarations.

The proof uses the existing source-library two-resolution formula directly.
Products use the source library's general K-injective product constructions and
exact-functor product theorem, with exact pro-etale products transported through
the internal-module equivalence. Bounded models use the existing functorial
bounded injective resolution twice. The universal continuity clause follows from
the existing normalized qcqs continuity theorem, preserving the original cocone
legs through good truncation and pullback's colimit comparison.

Validation: the complete module compiled through `lcompile.py` with exit code 0,
no warnings, in 55.7 seconds. The existing seven definition bodies and theorem
signature were compared with the shared source and are unchanged. No source-library
files are modified. All Lean lines satisfy the 100-character limit.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.CondensedRing.closed_restriction_derived_operations`
(blueprint `lem-sfb-closed-restriction-derived-operations`).
Added 0 holes; split off 0 statements. No `sorry` remains in the item module,
and no additional Lean module is delivered. The theorem is proved from the named
existing dependencies, as required by stage 3; this is a proof rather than a
new-hole decomposition.

## No longer needed

Removed private imports:

- `Sheaf.CategoryTheory.ExactInputDerivedTransformation`:
  use the existing `rightDerivedPullback_app_Q_obj` and the derived units'
  shift compatibility directly. The dependency
  `lem-sfb-exact-input-derived-transformation` and its arbitrary right-derived
  pair interface `def-sfb-right-derived-functor` are unnecessary on this route.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`:
  the module-object category already has the native Grothendieck instance.
  Native functorial degreewise injective resolutions supply the required objects;
  the extra dependency `prop-pur-kinjective-resolutions-exist` is unnecessary.
- `Sheaf.Algebra.Homology.KInjectiveProductsTermwise`: use the existing generic
  source-library product theorems directly, so the specialized dependency
  `lem-pc-ringed-space-product-kinjective` is unnecessary here.
- `Sheaf.AlgebraicGeometry.ProEtaleProductsDerived`: use exact products plus
  the source library's `preservesLimitsOfShape_discrete_mapDerivedCategory`;
  the dependency `det-pe-products-derived` is unnecessary here.
- `Sheaf.CategoryTheory.KInjectiveComputes`: the native theorem
  `CochainComplex.isKInjective_of_injective` applies to the bounded injective
  complexes, so `lem-sp-kinjective-computes` is unnecessary here.

Removed the obsolete top-level tool approvals for `det-pe-products-derived`,
`lem-pc-ringed-space-product-kinjective`, `prop-pur-kinjective-resolutions-exist`
and `lem-sp-kinjective-computes` in the node copy.

These are removals from this proof's dependencies, not withdrawals of modules
still used elsewhere. No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The proposed general exact-input derived-transformation dependency is unnecessary:
the adopted source library already proves the precise two-resolution formula for
the actual transformation used in this statement. The product argument likewise
has generic proved source-library infrastructure, avoiding the specialized
statement-only dependencies. The mathematical conclusions and the reviewed
representative normalization are retained, including the restriction square only
on the simultaneous functorial chain model.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
