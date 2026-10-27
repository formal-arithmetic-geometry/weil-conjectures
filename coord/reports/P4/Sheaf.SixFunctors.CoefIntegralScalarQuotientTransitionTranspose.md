## What changed

Proved `quotient_reduction_transition_transpose` by exposing completion transport with
adjunction hom-equivalence naturality and reducing to a residual finite reduction and
tensor-square mate calculation. Added the proof-only import
`Sheaf.SixFunctors.CoefIntegralScalarQuotientTransitionTransposeCore`.

## Proved and sorry left

The item theorem `WeilConjectures.IntegralFiniteExtension.quotient_reduction_transition_transpose`
is proved. One strictly simpler intermediate theorem remains sorry:
`quotient_reduction_transition_transpose_core`, in the new node
`lem-sf-integral-scalar-quotient-transition-transpose-core`.

## No longer needed

No planned proof dependencies were pruned. The proof uses the finite-extension models,
scalar-reduction exchange, and the new residual mate node.

## Where the brief, the DAG or earlier work was wrong

The original split treated the entire transpose equality as the lowest available mate
calculation. Completion naturality separates a residual finite tensor calculation from
the outer hom-equivalence transport; the DAG now records that lower calculation as a
separate statement.

## New nodes

`lem-sf-integral-scalar-quotient-transition-transpose-core` records the residual mate
calculation after completion transport. Its Lean declaration is in
`lean/Sheaf/SixFunctors/CoefIntegralScalarQuotientTransitionTransposeCore.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefIntegralScalarQuotientTransitionTranspose": "048db70dc88ca6f7757a358c64f98dfce3eff3a0", "Sheaf.SixFunctors.CoefIntegralScalarQuotientTransitionTransposeCore": "eca64ad3431a1734a1e15ec451dd34af12858859"}, "results": {}, "time": "2026-10-28T07:10:08+0800", "transitive": 0, "version": 1}
```

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
