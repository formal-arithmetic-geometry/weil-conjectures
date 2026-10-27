## What changed

The assigned theorem now assembles two strictly smaller named assertions: sourcewise universality and etale restriction coherence. The target proof itself is complete Lean, while the two partial assertions remain explicit theorem-level `sorry`s in separate modules. No existing module outside this item was changed.

## Proved and sorry left

Closed `AlgebraicGeometry.Scheme.finitePerfectAdicEtaleConstant_normalization` by applying the two partial assertions to the universal and coherence fields.

Added two split-off holes:

- `AlgebraicGeometry.Scheme.finitePerfectAdicEtaleConstant_universal`, node `lem-weil-pbc-finite-perfect-adic-constant-normalization-universal`.
- `AlgebraicGeometry.Scheme.finitePerfectAdicEtaleConstant_coherence`, node `lem-weil-pbc-finite-perfect-adic-constant-normalization-coherence`.

Both are strictly simpler fields of the target structure and have source and proof plans in their docstrings and DAG nodes. No definition contains `sorry`.

## No longer needed

None. The target's original proof dependencies remain represented in the two split theorem plans; no module was withdrawn or pruned.

## Where the brief, the DAG or earlier work was wrong

The original one-step proof plan conflated two independent obligations: initiality of each pulled-back structured arrow and naturality under etale restriction. The target can be assembled from these separate statements, but the current library has no single theorem proving either finite-perfect obligation end to end. The target statement is unchanged.

## New nodes

`lem-weil-pbc-finite-perfect-adic-constant-normalization-universal` records sourcewise universality of the explicit constant transition.

`lem-weil-pbc-finite-perfect-adic-constant-normalization-coherence` records its etale restriction coherence.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FinitePerfectAdicConstantCoherence": "6351347dca0fb693fa4b903e3c8da3017503bfb3", "Sheaf.Paper.FinitePerfectAdicConstantNormalization": "d1ded0f7d17708d681bd5d52ff685b706373f936", "Sheaf.Paper.FinitePerfectAdicConstantUniversal": "8bc54a6e570ae1446d18f733eb7af79e21741551"}, "results": {}, "time": "2026-10-28T00:04:13+0800", "transitive": 0, "version": 1}
```

## Second reading by J8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
