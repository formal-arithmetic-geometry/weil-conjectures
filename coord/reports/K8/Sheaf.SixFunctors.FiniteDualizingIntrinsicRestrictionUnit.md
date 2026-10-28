## What changed

Proved `WeilConjectures.finiteDualizingIntrinsicRestriction_unit` in
`Sheaf.SixFunctors.FiniteDualizingIntrinsicRestrictionUnit`, preserving its statement,
public import and docstring. Added a private proof import of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars` for
`Functor.mapDerivedCategorySquareIso_hom_app_id`.

Private proved helpers establish surjectivity and naturality of scalar-unit sections,
identity normalization of the ordinary comparison, and transport of its derived identity
square along equality of exact restriction functors. The main theorem specializes this to
the identity quotient, uses the existing HEq characterization of the specified intrinsic
comparison, and applies extensionality. The item's node now records these steps.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.finiteDualizingIntrinsicRestriction_unit`
(node `lem-coef-dualizing-realization-restriction-unit-intrinsic`).
Added zero holes; zero sorries remain in the delivered module. No split-off statements.
All six private helpers have complete proofs.
The complete module compiled without warnings via `lcompile.py` in 26.2 seconds
(exit code 0), within the 60-second per-file limit.

The argument works for n = 0, uses no nonzero-ring hypothesis in its generic helpers,
and does not require nonemptiness of the scheme or any choice of geometric points.

## No longer needed

None. The proof uses all three original dependency nodes: finite dualizing data,
normalized DVR towers and normalized origin scalar comparisons. No existing import,
module or DAG dependency is removed. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement repair was needed. The former plan is realized directly using the existing
exact-derived identity-square theorem; no further decomposition is required.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.FiniteDualizingIntrinsicRestrictionUnit": "f7b41c0bd5712cbe4f4514b5a90562de8c356b5a"}, "results": {"Sheaf.SixFunctors.FiniteDualizingRealizationRestrictionUnit": {"hash": "73864116e2ca026174da4afad14d67fdb78d1445", "status": "OK"}}, "seconds": 129, "time": "2026-10-28T12:04:23+0800", "transitive": 0, "version": 1}
```

## Second reading by K8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
