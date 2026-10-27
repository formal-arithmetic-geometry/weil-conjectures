## What changed

Marked `WeilConjectures.RationalVerdier.datum_naturality_of_kflat` as
`STATEMENT-DISPUTED` in the delivered module.  The source compiles unchanged apart
from this diagnostic comment.

## Proved and sorry left

No holes were closed and no new holes were added.  The single hole left is
`WeilConjectures.RationalVerdier.datum_naturality_of_kflat`, in node
`lem-coef-rational-verdier-datum-naturality`.

## No longer needed

None.  The existing import and proof-dependency node remain necessary for the
statement's types and for a future corrected descent theorem.

## Where the brief, the DAG or earlier work was wrong

The theorem assumes naturality only for pairs of literal K-flat representatives,
but `IntegralVerdier.SignedSymmetry` stores an unconstrained family
`swap K L` for arbitrary derived objects.  A component at a non-K-flat object can be
changed by an automorphism without changing the `representative` field or `hflat`,
while changing the displayed arbitrary-derived naturality equation.  Therefore the
localization argument in the proof prose cannot establish this statement.  A valid
repair needs an additional naturality or transport condition on `A.symmetry.swap`
(or a statement restricted to K-flat representatives) before the hole can be proved.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.RationalVerdierDatumNaturality": "2995a39f8ff9fced14b44525cb8a9a7a1d1f84c7"}, "results": {"Sheaf.SixFunctors.RationalVerdierDatum": {"hash": "164615386e1467e18c23406d7a9b67282fff944c", "status": "OK"}}, "seconds": 15, "time": "2026-10-28T06:43:29+0800", "transitive": 0, "version": 1}
```

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
