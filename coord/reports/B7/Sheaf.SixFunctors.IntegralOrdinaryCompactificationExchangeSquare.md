## What changed

Proved `WeilConjectures.IntegralSystemRealization.ordinaryCompactificationExchangeSquare`
by specializing the existing `ordinaryBasicSquare` to `BasicPair.compactExchange`.
The constructor records exactly the two prescribed exchange components and the original
compactification data. The theorem's signature is unchanged.

Added the private proof import `Sheaf.SixFunctors.OrdinaryBasicSquare` and removed the
unused private mate/pullback/open-base-change calculations. Updated the assigned node's
proof and proof dependencies to match this specialization. No public definition,
instance, attribute, import, or other module is changed. No new node is introduced.

## Proved and sorry left

Closed the one original hole in
`WeilConjectures.IntegralSystemRealization.ordinaryCompactificationExchangeSquare`
(node `lem-sf-integral-ordinary-compactification-exchange-square`).
Holes closed: 1. Holes added: 0. Holes left in the assigned module: 0.

The proof uses the existing theorem
`WeilConjectures.IntegralSystemRealization.ordinaryBasicSquare`
(node `lem-sf-integral-ordinary-basic-square`), whose existing `sorry` is unchanged.
This delivery proves the specialization from that declared theorem; it does not claim
that the transitive proof is already free of `sorry`.

## No longer needed

Removed the direct private imports:

- `Sheaf.SixFunctors.IntegralOrdinaryCanonicalIsoSquare`
- `Sheaf.SixFunctors.OpenReconstructionEffectivity`
- `Sheaf.SixFunctors.TensorAdjunctionReductionSquares`

The assigned proof no longer needs its private `mate_pasting_square`,
`proper_pull_coeff`, `push_reduction_eq_mate`, `proper_exchange_eq_mate`,
`proper_exchange_coeff`, or `open_beta_coeff` helpers. Their calculations are not
needed to specialize the existing generic coefficient square.

The corresponding three old proof-dependency nodes are removed from this node's
immediate proof dependencies. They remain part of the generic basic-square theorem's
planned proof and are also used elsewhere; no claim of global withdrawal is made.
No module or DAG node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The earlier plan attempted concrete mate pasting and recorded a kernel conversion
timeout. The current library already exposes the more general `ordinaryBasicSquare`
in a separately importable module. `BasicPair.compactExchange` gives this exact
specialization, so the local concrete pasting is unnecessary. The new import has no
Lean import path back to this module. The coefficient compatibility unit and both
prescribed structural maps are preserved.

The general basic-square theorem remains an existing proof obligation. Its current
DAG includes broad pre-existing dependency paths through definitions back to this
family; this delivery does not introduce a Lean import cycle or add a new holed
statement. The report distinguishes removal of immediate dependencies from global
pruning for that reason.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralOrdinaryCompactificationExchangeSquare": "890bc9710409468145e22d381145cf003c157840"}, "results": {"Sheaf.SixFunctors.IntegralOrdinaryCompactificationSquares": {"hash": "8b89f269177bdb75db7085017ff39c046c316186", "status": "OK"}}, "seconds": 35, "time": "2026-10-28T06:35:37+0800", "transitive": 0, "version": 1}
```

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
