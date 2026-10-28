## What changed

Proved `WeilConjectures.integralAutomorphismCancellation_precomposition` in
`Sheaf.Paper.IntegralAutomorphismCancellationPrecomposition`, keeping its statement unchanged.
The private helpers construct the normalized ordinary identity comparison and prove its
unit and inverse-composition/counit equations on sections. Exact-derived pasting transfers
these equations. Composition compatibility, naturality of kappa, and the completed target
unit law then force the identity normalization. Expanding epsilon and cancelling the two
inverse kappa factors completes the requested equality.

Added proof imports for normalized geometric coherence, kappa naturality, and exact-derived
pasting. Updated the item's DAG proof and proof dependencies to record this argument.
No existing statement, definition, instance or public import was changed. The change record is `coord/changes/IntegralAutomorphismCancellationPrecomposition.md`.

## Proved and sorry left

Closed the sole original hole:
`WeilConjectures.integralAutomorphismCancellation_precomposition`
(node `lem-sf-integral-automorphism-cancellation-precomposition`).

Holes closed: 1. Holes added: 1. Sorries left in the item: 1 (`WeilConjectures.integralIdentityCompositorSections`). This is a strictly simpler split-off identity-compositor statement.
All private helper theorems and definitions are complete. The new public theorem supplies the remaining ordinary section equation.

## No longer needed

None. All three original proof dependencies are used. No imports were removed and no
nodes or modules are pruned. The additional exact-derived-pasting dependency is already
stated and proved in the library.

## Where the brief, the DAG or earlier work was wrong

No false statement or unit-route error was found. The previous proof plan referred to
normalized identity compatibility without a separate ready-to-apply Lean equation.
This delivery proves that compatibility from the existing composition, naturality,
and unit equations, with one strictly simpler ordinary section-compositor obligation; the derived normalization and cancellation are complete.

## New nodes

Added `lem-sf-integral-identity-compositor-sections`, the strictly simpler identity-compositor section equation used by the derived normalization proof. Its proof is left as the one documented sorry in its own module.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntegralAutomorphismCancellationPrecomposition": "0409e862c5b4344e775db7e81902de382cd2e822", "Sheaf.Paper.IntegralIdentityCompositorSections": "482a28e411594439fae795e14735f4a1b11803ec"}, "results": {"Sheaf.Paper.IntegralAutomorphismCancellationNormalization": {"hash": "d5c94cc700c1e1f8374f3a7fa0fc82f06f8415c9", "status": "OK"}}, "seconds": 15, "time": "2026-10-28T11:15:34+0800", "transitive": 0, "version": 1}
```

## Second reading by W6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
