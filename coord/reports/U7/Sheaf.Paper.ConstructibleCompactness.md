## What changed

Proved `AlgebraicGeometry.ProEtale.constructible_compactness` for both coefficient rings,
following the existing five-step proof plan. Private proved helpers identify compactness
in a full subcategory with the ambient Hom comparison, prove that canonical truncations
preserve coproducts, transfer the finite-window equivalence through coprojections, and
extend compactness from sheaves to bounded constructible complexes. The final step
restricts the comparison to the localizing closure of Dbc. The finite-field
characteristic follows from the datum's cardinality and its injective algebra map.

All existing public signatures, definitions and docstrings are unchanged. Added only
private proved helpers and proof imports. Updated the existing node's proof to record
the library coproduct and finite Postnikov arguments actually used. No new nodes.
The module compiles cleanly through lcompile.py (10 seconds).

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.ProEtale.constructible_compactness`
(node `sk-thm-constructible-compactness`). Holes closed: 1; holes added: 0.
No `sorry` remains in the delivered module. The proof uses existing stated dependencies,
including their recorded open obligations; this delivery adds no split-offs.

## No longer needed

Removed proof imports `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits` and
`WeilConjectures.CategoryTheory.TruncationTriangle`. The first is a broad bundle of
truncation, telescope, exact-couple and stalk interfaces; only its existing ordinary
Mathlib truncation definitions are used, already available through the other imports.
The definition node `def-kun-truncations` remains for those same truncations.
The second module and node `lem-weil-pbc-truncation-triangle` are not required by this
proof: the proved `DerivedCategory.prop_of_bounded` performs the same finite Postnikov
induction in the ambient t-structure. Its proof uses the canonical truncation triangles.
Removed the obsolete `lem-weil-pbc-truncation-triangle` tool-use entry as well.
This preserves the unit's finite-extension route. No claim is made that these modules
are globally unreachable; other items may still import them.

## Where the brief, the DAG or earlier work was wrong

The DAG prescribed the complex-representative truncation triangle separately, although
an existing proved library theorem already packages the required finite induction.
The canonical truncation coproduct comparison can likewise be proved directly from
the t-structure API and the existing homology-preserves-coproducts instance. The same
bounded-family, finite-window, thick-closure and localizing-closure inputs are retained.
No statement or definition repair is required.

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
