## What changed

Proved three existing theorems in
`Sheaf.AlgebraicGeometry.NormalizedFiniteSplittingOperations`, without changing any
statement, definition, public import or global instance.

- `normalizedFiniteSplittings_products`: construct finite-constant limits using inverse-image
  preservation and the finite-set/constant-sheaf comparison. The supplied `fibreIso` and
  reflection of limits by the forgetful functor prove preservation by `D.fibre`.
  The argument covers the empty product.
- `normalizedFiniteSplittings_restrict`: reuse the underlying finite-constancy witness by
  definitional equality, identify the sections by `HEq.rfl`, and specialize the existing
  module-operation theorem to the scalar `a r`.
- `normalizedFiniteSplittings_scalar_natural`: scalar extension preserves the stalk colimit
  by its adjunction. Precomposition with each extended coprojection reduces the square to
  the two supplied germ equations and naturality of the sheafification unit.

Added private proof imports for action-limit reflection, finite-set limits, universe-lift
limits and finite-product closure of a full subcategory. Updated Steps 1, 2, 4 and 6 of
`lem-sfb-normalized-finite-splitting-operations` to describe these proofs. The remaining
steps and the dependency union remain needed for the five unfinished assertions.

Validation: `lcompile.py` compiled the complete final module successfully in 16.3 seconds,
with no errors or warnings. All lines are at most 100 characters.

## Proved and sorry left

Closed 3 of the original 8 holes, with no holes added and no split-off statements:

- `AlgebraicGeometry.ProEtale.normalizedFiniteSplittings_products`.
- `AlgebraicGeometry.ProEtale.normalizedFiniteSplittings_restrict`.
- `AlgebraicGeometry.ProEtale.normalizedFiniteSplittings_scalar_natural`.

The restriction proof depends on the still-unproved existing module-operation assertion;
this is a proof from the existing declared dependency, not a new decomposition.

Five original holes remain, all attached to
`lem-sfb-normalized-finite-splitting-operations`, with their original sources and complete
natural-language proof plans retained:

- `AlgebraicGeometry.ProEtale.normalizedFiniteSplittings_module`.
- `AlgebraicGeometry.ProEtale.normalizedFiniteSplittings_scalar`.
- `AlgebraicGeometry.ProEtale.normalizedFiniteSplittings_scalar_comp`.
- `AlgebraicGeometry.ProEtale.normalizedFiniteSplittings_refinement`.
- `AlgebraicGeometry.ProEtale.normalizedFiniteSplittings_refinement_comp`.

## No longer needed

Removed these unused private proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleSheafificationGeometricStalk`.
- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImageStalk`.

Their corresponding DAG dependencies remain in the proof plans of the unfinished scalar
and refinement assertions; no node or module is claimed to be globally unnecessary.
For the product theorem, uniqueness and descent calculations are unnecessary: its
categorical conclusion follows directly from the given natural stalk identification.
For scalar naturality, the existing `germ` fields suffice; no construction of a scalar
comparison or invocation of the scalar-existence theorem is needed.
The blueprint unit route is retained, with no withdrawals.

## Where the brief, the DAG or earlier work was wrong

No false statement or incompatible dependency was found. The original product-splitting
uniqueness argument can be replaced by the shorter categorical reflection argument.
The scalar-naturality argument needs no additional generator lemma: the preserved
colimit universal property supplies extensionality directly.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
