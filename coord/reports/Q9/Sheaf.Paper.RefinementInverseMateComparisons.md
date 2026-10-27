## What changed

Proved `AlgebraicGeometry.RefinementInverseMateData.refinement_inverse_mate_comparisons`
in `Sheaf.Paper.RefinementInverseMateComparisons`, with its statement and all definitions
unchanged. Added eight proved private helpers in the same module: component formulas,
inverse vertical pasting, the identity law, the explicit four-factor formula, composition
as natural transformations and isomorphisms, and invariance under further refinement.
The final proof equalizes parallel refinements and cancels their invertible comparisons,
then computes spans on a common refinement and cancels the middle inverse pair.
No imports changed and no other modules were adapted.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.RefinementInverseMateData.refinement_inverse_mate_comparisons`
(node `lem-pur-refinement-inverse-mate-comparisons`). All six conclusions are proved,
including the explicit four-factor expression. Zero holes remain and zero were added;
no statements were split off. Remote compilation succeeded without warnings.
`#print axioms` on the completed theorem reported exactly `propext`, `Classical.choice`,
and `Quot.sound`.

## No longer needed

None. All original imports remain needed for the statements and constructions.
The proof follows the existing node's inverse-pasting, compositor-naturality and
cofiltered-cancellation route; its two declared proof dependencies remain used.
No nodes or modules are pruned. Search found Mathlib's eventual-constant cone API,
but using it would require packaging the same functoriality and does not shorten the
explicit component calculation, so no additional proof dependency was imported.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error was found. The proof uses invertibility only on
the specified full subcategory. Empty subcategories cause no exception: componentwise
proofs are universally quantified over their objects. Identity and coincident endpoints
are covered by the same unit and cancellation arguments. Cofilteredness is used solely
to obtain equalizing arrows and common refinement objects; no geometric comparison for
other squares and no evaluation-detection hypothesis was introduced.

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
