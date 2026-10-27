## What changed

Completed `AlgebraicGeometry.ProEtale.intrinsicSiteHom_transport` by choosing a
K-injective representative of the second derived input, applying the representative-level
coefficient comparison, and transporting along the derived representative isomorphisms in
both variables. Added the private proof import
`Sheaf.Paper.IntrinsicSiteHomTransportRepresentatives` and updated the item node's proof
and proof dependencies accordingly. Added one representative-level split-off theorem in
its own module and node.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.ProEtale.intrinsicSiteHom_transport` in
`lem-sf-intrinsic-site-hom-transport`. The delivery adds one strictly lower-level hole,
`AlgebraicGeometry.ProEtale.intrinsicSiteHom_transport_representatives`, in node
`lem-sf-intrinsic-site-hom-transport-representatives`. It fixes chain representatives and
assumes the second is K-injective; the arbitrary-object assembly is proved in the item.

## No longer needed

None. The exact intrinsic realization and universe-lifted derived Hom imports remain used,
and the parent proof still follows its representative/localization route.

## Where the brief, the DAG or earlier work was wrong

The existing plan correctly reduces the statement to K-injective representatives, but it
had no Lean declaration for the coefficient-presentation comparison on those
representatives. The generic `derivedInternalHomOfUniverses_obj_iso` API handles the
intrinsic side after a representative is fixed, while no existing declaration identifies
that object with the fixed-scalar `derivedHom` after realization. That missing bridge is
split off as the representative-level node without changing the target statement.

## New nodes

`lem-sf-intrinsic-site-hom-transport-representatives` records the remaining comparison
for fixed chain representatives with a K-injective target. Its Lean declaration is
`AlgebraicGeometry.ProEtale.intrinsicSiteHom_transport_representatives` in
`Sheaf.Paper.IntrinsicSiteHomTransportRepresentatives`.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.IntrinsicSiteHomTransport": "de6911739e12353eade2107c2641297c16515128", "Sheaf.Paper.IntrinsicSiteHomTransportRepresentatives": "6f0ddaf228dc8d8a6322c89291e89f3fbaf4d77a"}, "results": {"Sheaf.Paper.FiniteConstructibleHom": {"hash": "cecba2eef9dca70e39a4b534d8d53a51c4787e90", "status": "OK"}, "Sheaf.Paper.TensorExchangeCtfDomains": {"hash": "cede8d1e5046fd53681787e14bb76c52d06d013c", "status": "OK"}}, "seconds": 88, "time": "2026-10-28T06:43:48+0800", "transitive": 0, "version": 1}
```

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
