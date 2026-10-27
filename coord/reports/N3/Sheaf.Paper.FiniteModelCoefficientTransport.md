## What changed

Copied the assigned module into the delivery sandbox and added a proved private helper
`finiteModel_constantComplex_mapIso`.  The helper uses the exact constant-module
functor and transports an arbitrary derived-category isomorphism through its
localization comparison.  The assigned theorem itself remains unchanged except for a
`STATEMENT-DISPUTED` comment recording the missing flatness hypothesis.

## Proved and sorry left

The private helper `finiteModel_constantComplex_mapIso` is proved.  The existing
`sorry` in `finiteModel_derivedRepresentative_transport` remains, because the stated
claim is false without a K-flat hypothesis on `P` (see the dispute comment and the
counterexample there).  No new `sorry` declarations were added.

## No longer needed

No imports or DAG proof dependencies were removed.  The helper uses the finite-model
data import and the exact constant-module functor interface.

## Where the brief, the DAG or earlier work was wrong

The assigned node and its docstring assert ordinary scalar extension of an arbitrary
complex is a representative of the left-derived scalar extension.  This requires a
K-flat (or equivalent) hypothesis on `P`, which is absent.  For `q : ℤ →+* ℤ/2` and
`P := (ℤ/2)[0]`, the derived extension has a nonzero Tor term while ordinary scalar
extension does not, so the claimed derived-category isomorphism cannot hold in
 general.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteModelCoefficientTransport": "59bd7e6cd2c25eff3a362bfad1d1cdb50ae681d5"}, "results": {"Sheaf.Paper.FiniteModelDerivedScalarComparison": {"hash": "222cfe6c493a3fbd26fecbade15607f09975ec97", "status": "OK"}}, "seconds": 6, "time": "2026-10-28T04:16:11+0800", "transitive": 0, "version": 1}
```

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
