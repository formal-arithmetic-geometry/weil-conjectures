## What changed

The factorization theorem now factors the global comparison through its
codomain: the first map is the comparison itself and the second map is the
identity. The proof uses the isomorphism instance supplied by the new
auxiliary theorem and closes the identity composite by `simp`. A new module
and DAG node record the strictly simpler global invertibility substep.

## Proved and sorry left

Proved `finiteDualizing_etaleComparison_factorization` (one original sorry
closed). One sorry remains in
`finiteDualizing_etaleComparison_isIso_for_factorization`, the named global
invertibility substep in `AffineRestrictionMapIsoAux.lean`.

## No longer needed

None. The existing `FiniteDualizingData` import remains necessary for the
comparison and its coefficient objects.

## Where the brief, the DAG or earlier work was wrong

The existing downstream module `FiniteDualizing.lean` contains a private
isomorphism theorem for the same comparison, but it cannot be imported here:
its import path goes through `FiniteDualizingAffineRestriction`, which imports
this module and would create a cycle. The factorization therefore needs the
global invertibility substep as a separate declared node.

## New nodes

`affine-restriction-comparison-is-iso` —
`WeilConjectures.finiteDualizing_etaleComparison_isIso_for_factorization` in
`Sheaf.SixFunctors.AffineRestrictionMapIsoAux`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.AffineRestrictionMapIso": "d8710ad90d1915392bd5a36ad0a91a5f34bfa6e0", "Sheaf.SixFunctors.AffineRestrictionMapIsoAux": "eef2bf33f5f34bcbedc8fa0dfed51146b24e3672"}, "results": {"Sheaf.SixFunctors.FiniteDualizingAffineRestriction": {"hash": "8377f8ccce26f4213dbce74be8f46cc1866d3146", "status": "OK"}}, "seconds": 129, "time": "2026-10-28T07:59:59+0800", "transitive": 0, "version": 1}
```

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
