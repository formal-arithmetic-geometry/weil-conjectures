## What changed

The assigned module privately imports two new statement modules and proves
`coordinate_section_product_recursion` from their supported-product and general
adjunction-composition equations. The inverse-Hom-bijection cancellation at rank
zero and the substitution at a successor are explicit Lean proofs. Existing
public signatures, definitions, public imports, and ordinary-witness proofs stay
unchanged. No other existing module is delivered.

## Proved and sorry left

Closed one of four original holes by decomposition:
`AlgebraicGeometry.ProEtale.AffineZeroPurity.coordinate_section_product_recursion`,
node `lem-pur-coordinate-section-product-recursion`.
The proved private helper `compactProduct_adjunct` cancels the fixed Hom bijection.

Added two holes, strictly separate parts of the argument:

- `AlgebraicGeometry.ProEtale.AffineZeroPurity.coordinate_supported_product_recursion`,
  node `lem-pur-coordinate-supported-product-recursion`: only the two supported equations;
- `AlgebraicGeometry.ProEtale.AffineZeroPurity.coordinateAdjunction_composition`,
  node `lem-pur-coordinate-adjunction-composition`: the specified compositor transposition for an arbitrary earlier arrow, with no
  supported-product equation or rank-zero clause.

Three original holes remain unchanged, all under
`lem-pur-coordinate-section-product-recursion`:

- `AlgebraicGeometry.ProEtale.AffineZeroPurity.coordinate_section_product_baseChange`;
- `AlgebraicGeometry.ProEtale.AffineZeroPurity.coordinate_section_product_permutation`;
- `AlgebraicGeometry.ProEtale.AffineZeroPurity.coordinate_section_product_exponent`.

There are three holes in the assigned module and two in the new modules, five
in this packet. This is a decomposition, not a net reduction of holes. No
hole is inside a definition.

## No longer needed

None pruned. No original imports, declarations or modules are withdrawn. The
parent's former direct Cartier, supported cup and projection dependencies for
Steps 1--5 are now carried by the supported-product node; they remain transitively
needed. The unit route stays the same.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction. The expanded Step 6 lacks a directly
applicable theorem for the specified compositor. A direct formal proof elaborated
but its defining compositor equation took over 100 seconds of kernel checking.
Generic categorical helpers and a definitionally identical generic-body refactor
were tried; the latter compiled alone in 31 seconds but did not resolve that
equation. The final packet restores every existing definition and isolates the
general adjunction-composition calculation with its full proof in words. It is
not the original theorem under another name: it permits an arbitrary earlier arrow and has no rank-zero clause or
supported-product recursion assumption or conclusion. The final statement uses
the named coordinate comparisons directly, avoiding their expensive unfolding
in the parent proof.

## New nodes

`lem-pur-coordinate-supported-product-recursion` records the original Steps 1--5,
only the supported equations, in `Sheaf.Paper.CoordinateSupportedProductRecursion`.
Its node and docstring give the Cartier/cup/projection proof, including empty base,
rank zero, and even shifts.

`lem-pur-coordinate-adjunction-composition` records Step 6's pasted-counit
identity in `Sheaf.Paper.CoordinateAdjunctionComposition`. Its source, bounded-origin
hypotheses, naturality proof and equality transport are explicit. These two nodes
are combined by the unchanged parent statement, not merely renamed. No existing
statement or definition changes, so no change record or consumer adaptation is
required.

## Second reading by Y8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
