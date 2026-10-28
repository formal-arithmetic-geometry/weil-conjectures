## What changed

Proved `AlgebraicGeometry.ProEtale.IsomorphismScalarTensor.finite_formula_of_unit`
in `Sheaf.Paper.IsomorphismScalarFiniteComparisonExtension`, with its statement
unchanged. Added six proved private helpers for sheafified tensor balancing,
scalar multiplication, and compatibility of coefficient transport with the
finite scalar quotient map. The argument applies the finite comparison's
module linearity to the unit tensor and then uses the assumed unit formula.

Added only the proof import
`import all Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison`
to access its proved private `constantMap_naturality`. The original public import
is unchanged. No existing definition, public declaration, instance, or attribute
was changed. Updated the item's proof steps and dependencies to match this proof.
The full module compiled successfully through `lcompile.py` in 16.0 seconds.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.IsomorphismScalarTensor.finite_formula_of_unit`
(node `lem-weil-isomorphism-scalar-finite-comparison-formula-extension`).
There are zero `sorry` occurrences left in the item, and zero holes or split
statements added elsewhere. All six new private helpers have complete proofs.

## No longer needed

The planned proof dependency
`lem-weil-isomorphism-scalar-quotient-chain-squares`, realized by
`Sheaf.Paper.IsomorphismScalarQuotientChainSquares`, is not needed for this
extension step: ordinary tensor balancing, naturality of the constant-sheaf
coefficient comparison, and the given unit formula suffice. Removed it from this
node's proof dependencies. This does not withdraw that module or remove its
other consumers; the unit-existence argument may still need it.

No original imports were removed. No new modules are needed. The unit predicate
and the original unit route are retained.

## Where the brief, the DAG or earlier work was wrong

The stated scalar-linearity route is correct, but quotient-chain squares are
unnecessary for this conditional extension theorem. One must use the actual
finite-coefficient module morphism underlying the comparison: its restricted
completed-coefficient presentation hides the finite scalar action. The proof
makes the inverse-image scalar action and coefficient transport explicit, and
proves the required local tensor identities directly from the sheafification
unit's linearity and tensor-product balancing. No statement repair is needed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 INFRA.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IsomorphismScalarFiniteComparisonExtension": "bf27dab5f261dc7484954008311c7d79748ff6dd"}, "results": {"Sheaf.Paper.IsomorphismScalarFiniteComparisonFormula": {"hash": "89226d90db73db521bd78b64177865a5f7ed5324", "status": "INFRA"}}, "seconds": 88, "time": "2026-10-28T11:12:51+0800", "transitive": 0, "version": 1}
```

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
