## What changed

Proved `CategoryTheory.InternalAbelianSheafModule.ringedSiteFreeMatrixScalarExtension`
without changing its statement or any existing definition. The construction uses the
canonical biproduct projections and sums of inclusions, linearity through the existing
section-module functor, and the mixed-bimodule right unitor assembled through finite
biproducts. All added helpers are private and proved in the item module.

## Proved and sorry left

Closed the one existing hole in
`CategoryTheory.InternalAbelianSheafModule.ringedSiteFreeMatrixScalarExtension`
(node `lem-sfb-ringed-site-free-matrix-scalar-extension`). No holes added or split off;
no `sorry` remains in the delivered module.

## No longer needed

No imports or modules are removed. The proof does not use the direct rank-n
sheafification/balanced-map construction of the old plan: the existing relative-tensor
right unitor and preservation of biproducts give the same normalized map. The separate
proof dependency `def-weil-pbc-sheafification` is no longer directly needed by this
node; the sheaf tensor and internal/sectionwise equivalence still use sheafification.
No withdrawal of that node or its module is requested.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The previous plan was longer than necessary:
the existing bimodule right unitor already proves the regular-module comparison.
The node's proof steps now record the rank-one and finite-biproduct argument.

## Second reading by S6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
