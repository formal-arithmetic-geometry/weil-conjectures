## What changed

Implemented `finiteScalar_exists` by assembling the finite scalar preservation and Tor-interval
packages, the ambient derived scalar shift, and the full-subcategory lift. The equality
realization is definitional, and its shift compatibility is obtained from the canonical
full-subcategory comparison. The two substantive preservation obligations are split into
the child theorem modules listed below.

## Proved and sorry left

Closed the `finiteScalar_exists` sorry. Two strictly smaller named obligations remain:

- `WeilConjectures.ExceptionalFiniteScalar.finiteScalar_preserves`
- `WeilConjectures.ExceptionalFiniteScalar.finiteScalar_torInterval`

## No longer needed

The parent proof no longer directly invokes the old proof-plan dependencies
`lem-sf-flat-model`, `lem-pur-derived-change-of-rings`, and
`lem-sf-comparison-tor-amplitude`; those declarations remain recorded as dependencies of
the two split child nodes, whose proofs are the pending work.

## Where the brief, the DAG or earlier work was wrong

The original parent proof plan treated preservation and Tor-interval transport as one
unreduced obligation. They are independent strictly smaller statements, so the parent
now combines them and handles only the categorical lift and shift bookkeeping.

## New nodes

- `lem-sf-exceptional-finite-scalar-preserves`
- `lem-sf-exceptional-finite-scalar-tor-interval`

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalFiniteScalar": "bed4ef1c7a6a71f2eecc050d86cf2d2cc2119054", "Sheaf.Paper.FiniteScalarPreservation": "dc093d0018bc6099525e3c557d1bcbaae2bc73fe", "Sheaf.Paper.FiniteScalarTorInterval": "08334f68fb3c88e99666e3ffcfa67da1283f37b4"}, "results": {"Sheaf.Paper.ExceptionalFiniteScalarMates": {"hash": "4168aa4eb3bb039e4b8b0d4996648abd6ba56903", "status": "OK"}}, "seconds": 13, "time": "2026-10-28T03:56:58+0800", "transitive": 0, "version": 1}
```

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
