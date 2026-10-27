## What changed

Replaced the remaining proof hole in `compactProductExtension_isIso` in
`Sheaf.AlgebraicGeometry.CompactProductArrows`. Two proved private helpers establish
the open projection formula for abstract coefficients and identify the exterior
product of the zero extensions with an extension by zero along the product open.
The original comparison is the inverse restriction isomorphism mapped by extension
by zero, followed by the counit at an object in its essential image, so both factors
are invertible. All existing signatures, definitions, attributes and public imports
are unchanged.

Added proof imports of the upstream open projection-map, tensor symmetry,
derived open base-change and open-composition modules. Updated the owning node's
proof and dependencies to describe this argument.

Validation: the complete proof compiled through `lcompile.py` in 26.6 seconds.
Removed the one unused-section-variable warning from the private helper before
the final delivery compile and axiom probe.

## Proved and sorry left

Closed 1 of 1 existing holes:
`AlgebraicGeometry.Etale.compactProductExtension_isIso`
(node `def-pur-compact-product-arrows`). Added 0 holes; 0 remain in the item.
The private helpers `compactProductProjection_isIso` and
`compactProductTensorIso` are proved completely. No split statements were added.

## No longer needed

No existing imports, nodes or modules are withdrawn. No pre-existing proof
dependencies were removed (the owning node previously had no proof steps).
A separate geometric-stalk tensor calculation is unnecessary: abstract open–closed
conservativity, base change and projection formulas give the required result.
The upstream module-coefficient compact-support Kunneth theorem is not imported;
only its shorter local extension-by-zero argument is generalized.

## Where the brief, the DAG or earlier work was wrong

The owning definition node had an empty proof plan despite the remaining
invertibility obligation. Its theorem docstring suggests geometric stalks;
the proof now uses the existing abstract-coefficient open–closed conservativity
API instead. The upstream projection-isomorphism instance assumes concrete
coefficients, so it cannot directly discharge this item's generic statement.
The private proof establishes the same projection map's invertibility without
those additional assumptions. No mathematical statement or construction changed.

## Second reading by V9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
