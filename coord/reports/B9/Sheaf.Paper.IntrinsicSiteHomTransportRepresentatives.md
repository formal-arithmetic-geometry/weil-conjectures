## What changed

Proved `AlgebraicGeometry.ProEtale.intrinsicSiteHom_transport_representatives` by composing a chain-level comparison with the generic intrinsic Hom representative isomorphism. The proof installs preservation of K-injective complexes from the exact equivalence `finiteCoefficientIntrinsicRealization`. Added the strict intermediate module `Sheaf.Paper.IntrinsicSiteHomTransportChain` for the representative chain comparison.

## Proved and sorry left

Closed the target sorry in `AlgebraicGeometry.ProEtale.intrinsicSiteHomTransportRepresentatives`.

Added one strictly simpler split-off sorry in `AlgebraicGeometry.ProEtale.intrinsicSiteHomTransportChain`: the realization of the fixed-coefficient derived Hom is identified with the localization of the intrinsic Hom complex on the realized complexes.

## No longer needed

None. The generic intrinsic representative comparison, finite-coefficient intrinsic realization, and fixed-coefficient derived Hom declarations remain needed by the delivered proof and its split-off statement. No imports or DAG nodes were pruned.

## Where the brief, the DAG or earlier work was wrong

The original proof plan omitted the explicit chain-level bridge between the fixed-coefficient realized derived Hom and the intrinsic Hom complex. The target proof cannot apply the generic representative theorem until that bridge is stated, so it is split off as the strictly simpler chain-comparison node.

## New nodes

Added `lem-sf-intrinsic-site-hom-transport-chain` and its module `Sheaf.Paper.IntrinsicSiteHomTransportChain`. Its conclusion is the localization-level Hom-complex comparison, which is strictly simpler than the target's generic derived internal Hom conclusion. The accompanying change record is `coord/changes/intrinsic-site-hom-transport-chain.md`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntrinsicSiteHomTransportChain": "fa100c1edc8d9f91f0d7131db6947e1fa8617d6e", "Sheaf.Paper.IntrinsicSiteHomTransportRepresentatives": "7688b7a7c2b2281e684118e07280d35ac8c85940"}, "results": {"Sheaf.Paper.IntrinsicSiteHomTransport": {"hash": "de6911739e12353eade2107c2641297c16515128", "status": "OK"}}, "seconds": 14, "time": "2026-10-28T09:51:27+0800", "transitive": 0, "version": 1}
```

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
