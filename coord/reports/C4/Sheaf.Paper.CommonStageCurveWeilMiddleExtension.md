## What changed

In `Sheaf.Paper.CommonStageCurveWeilMiddleExtension`, prove the ordinary Weil
inverse-image adjunction and the comparison of its chosen right adjoint with the
ordinary geometric right adjoint after forgetting Frobenius. The existing
geometric ordinary adjunction is lifted using the canonical Frobenius square and
`IsoAlgebra.mapOfNatIsoAdjunction`. Explicit private pair-category presentations
connect fixed pairs in the heart to heart-carrier fixed pairs. The inverse
Frobenius pullback is t-exact, so the heart Frobenius functors are equivalences
and their right-adjoint mate is invertible. Uniqueness of right adjoints gives
the forgetful comparison.

Add proof-only imports of `IsoAlgebraAdjunction`, `Adjunction.Restrict`, and
`IsomorphismFieldTransport`. All original public signatures, definitions and
public imports remain unchanged. Retain the landed arithmetic geometry proof.
Update the existing node's proof, proof dependencies and proof origin to record
this route. Abstract private helpers avoid unfolding the large constructible
categories during category-theoretic calculations.

## Proved and sorry left

Close two of the three original holes, without adding holes:

- `WeilConjectures.qbarCurveWeilPull_isLeftAdjoint`.
- `WeilConjectures.qbarCurveWeilOrdinaryPushforward_forget`.

The only remaining hole is
`WeilConjectures.qbarAffineWeilShift_forget`, node
`def-wf-middle-extension`, with its original statement and proof docstring.
`WeilConjectures.qbarAffineArithmeticGeometry` was already proved by G7 and its
proof is preserved. This is a proof from existing declarations, including the
existing postponed geometric ordinary-adjunction theorem; no split-off theorem
is introduced.

## No longer needed

None. Both original public imports remain needed. No original dependency, node,
module, declaration, or unit route is withdrawn. The new proof uses the existing
fixed-pair adjunction instead of expanding the sheaf-level equivariant
adjunction calculation again.

## Where the brief, the DAG or earlier work was wrong

The old proof metadata recorded only G7's arithmetic geometry proof. It now also
records the two ordinary direct-image proofs and the dependencies actually used.
The ordinary geometric adjunction already packages constructibility, so it need
not be reproved here. No statement discrepancy was found.

For the remaining affine shift comparison, the source library's
`nonempty_iso_artinSchreierSheafOf_one` identifies the uncompleted trivial
character sheaf with the unit. Applying it to the present completed,
rationalized, common-stage line still needs comparisons through completion,
pullback, tensor and signed shifts. This delivery leaves that original theorem
open rather than introducing another name for the same obligation.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
