## What changed

Proved `WeilConjectures.MixedCupCoefficientChange.reducedGood` in
`Sheaf.Paper.MixedCupTensorNormalization`. The ordinary reduction functor's recorded
object and map equations identify it with change of rings along the completed
coefficient projection. The existing independent-universe change-of-rings theorem
then supplies K-flatness and flatness of all terms. The canonical tensor-presentation
isomorphism converts termwise exactness in each direction, and the existing
independent/live K-flat equivalence supplies the predicate used by the finite tensor
model. Added two private proof imports for these existing results. Updated the node's
proof, proof dependencies and proof origin to record this specialization.

Validation: the final module compiled with exit code 0 and no warnings through
`lcompile.py` (31.3 seconds). Both added imports passed `import_direction.py may`.
The delivered Lean has zero sorry tokens and all lines fit the 100-character limit.

Both normalization definitions, all declaration signatures, and the unit route are
unchanged. The argument assumes neither flatness of the quotient ring map nor any
boundedness of the representative, and works for the zero representative and every
finite level including n = 0.

## Proved and sorry left

Closed 1 original hole:
`WeilConjectures.MixedCupCoefficientChange.reducedGood`
(node `def-sf-mixed-cup-tensor-normalization`).

No holes added or split off. No sorry remains in the delivered module.
The proof specializes the already proved
`SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients`;
it introduces no substitute existence assertion.

## No longer needed

None. No imports, nodes or modules are withdrawn. The original public imports supply
the existing normalization interface and remain unchanged. The node had no numbered
proof plan or proof dependencies to prune; the added proof records the theorem now used.

## Where the brief, the DAG or earlier work was wrong

The node had an empty proof list although the module contained the postponed
`reducedGood` theorem. Its docstring's proposed argument is already implemented by
the existing change-of-rings theorem, so no new intermediate theory was necessary.
The stage-3 proof plan now records that application and its predicate conversions.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
