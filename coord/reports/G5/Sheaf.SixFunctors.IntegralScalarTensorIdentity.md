## What changed

Proved `WeilConjectures.PurCompactSupport.scalarTensor_identity` in
`Sheaf.SixFunctors.IntegralScalarTensorIdentity`, preserving its statement and public imports.
Private helpers compute the ordinary unit on sections, its signed total tensor equation,
the exact identity localization factorization, and the derived unit on K-flat complexes.
Fully faithful restriction to representative pairs then proves the natural-transformation
identity, and cancellation gives the requested multiplication equation. The DAG proof now
records those steps. Proof imports expose the existing private representative and total APIs.

## Proved and sorry left

Closed the sole hole: `WeilConjectures.PurCompactSupport.scalarTensor_identity`
(node `lem-sf-integral-scalar-tensor-identity`). No holes added or split off; no sorry remains
in the delivered module. The private helper definitions use the existing uniquely normalized
restriction isomorphism and conjugation, with no postponed construction.
The complete item compiled without errors or warnings through `lcompile.py` in 53.6 seconds.

## No longer needed

None. Both declared dependencies are used: the normalized scalar tensor balancing and the
identity scalar multiplication unit. No unit route, module, or public import is pruned.

## Where the brief, the DAG or earlier work was wrong

The existing normalization and representative descent APIs suffice for a direct proof.
No further split of this obligation is needed. No statement or definition repair was made.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralScalarTensorIdentity": "abd8648a6b45216bf2ec13489f330bb7d1901208"}, "results": {"Sheaf.SixFunctors.CoefIntegralFiniteExtensionIdentityE": {"hash": "ca294c8ba45ddc1d2da4d09f787f1ec597d94f0a", "status": "OK"}}, "seconds": 87, "time": "2026-10-28T12:16:18+0800", "transitive": 0, "version": 1}
```

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
