## What changed

Proved `AlgebraicGeometry.ProEtale.AdicCompletion.internal_quotient_principal_cone_comparison`
with its original signature and complete augmentation equality. Added the proved one-level
lemma `internal_principal_cone_level_augmentation` in its own module and recorded its node.
No definitions, existing signatures, public imports, targets, or consumers change.

The one-level proof works directly in internal modules. It identifies the specified scalar
by pointwise extensionality, transports the coefficient short exact sequence through the
monoidal unit comparison, and uses flat-term K-flat resolutions to prove the normalized
cone augmentation is a quasi-isomorphism. The main proof establishes the strict tower and
unit equations, takes exact countable products, applies cone-triangle comparison, shifts,
and identifies the quotient mapping cocone with the fixed Roos coordinates. Both Roos
coordinates are checked, retaining the prescribed zero homotopy.

Proof-only imports expose the existing private coefficient and Roos APIs with `import all`.
The generic product/cone and zero-lift arguments are private proved helpers, adapted from
the already proved section-module comparison; that section-module module is not imported.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.ProEtale.AdicCompletion.internal_quotient_principal_cone_comparison`
(node `lem-pe-internal-quotient-principal-cone-comparison`).

Added 0 holes. The new
`AlgebraicGeometry.ProEtale.AdicCompletion.internal_principal_cone_level_augmentation`
(node `lem-pe-internal-principal-cone-level-augmentation`) is proved.
There are no remaining `sorry`s in either delivered Lean module, and no split-off holes.

## No longer needed

No original public import was removed. The direct internal proof does not need these
planned proof dependencies:

- `lem-pe-internal-section-tensor-comparison` /
  `Sheaf.CategoryTheory.InternalSectionTensorComparison`: no section-module transport.
- `lem-cbc-regular-quotient-cone-augmentation` /
  `Sheaf.Algebra.Homology.RegularQuotientConeAugmentation`: the normalized augmentation
  is proved directly in the internal category using the same short-exact cone argument.
- `lem-sfb-internal-section-scalar-adjunction` /
  `Sheaf.CategoryTheory.InternalSectionScalarAdjunction`: no scalar-adjunction transport.
- `lem-pur-principal-cone-exact-equivalence` /
  `Sheaf.Algebra.Homology.PrincipalConeExactEquivalence`: no equivalence of coefficient
  categories is used.
- `lem-pur-integral-principal-cone-quotient-comparison` /
  `Sheaf.Paper.IntegralPrincipalConeQuotientComparison`: its generic cone/product proof
  is adapted privately without importing the section-module comparison.

The existing `lem-pc-source-module-kflat-resolution` remains needed by the new level node;
it supplies the generic flat-term K-flat resolution. The coefficient-resolution and
DerivedCompletion nodes remain needed. No module is withdrawn, and these local dependency
removals do not claim that other consumers no longer need the named modules.

## Where the brief, the DAG or earlier work was wrong

The planned equivalence with section modules is unnecessary. Internal modules already have
categorical flat resolutions, exact countable products, and the coefficient short exact
sequence. Working directly avoids the section-ring, scalar-adjunction and completed-ring
identifications while preserving the exact scalar, quotient, transitions and augmentation.

The new level statement was checked at n=0 (exponent one), the zero complex, and the empty
scheme. Its proof requires only K-flatness of P, not flatness of its individual terms.
The blueprint unit route and all target statements are unchanged.

## New nodes

`lem-pe-internal-principal-cone-level-augmentation` states only the normalized comparison
at one fixed positive quotient. Its proof is complete. It has no products, tower,
completion, derived isomorphism, or augmentation-comparison conclusion of the parent.
The parent separately proves transition compatibility and the entire product/cone argument.
No change record is required because no existing interface or definition changes.

Validation: the new level module compiled without errors or warnings in 9.3 seconds,
and the main module compiled without errors or warnings in 6.7 seconds through lcompile.py.
Each delivered Lean file has zero `sorry`s and no lines exceeding 100 characters.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
