## What changed

Added the proof-only import `Sheaf.Paper.RationalP1ScalarChernSomeRaw`. The assigned theorem unfolds the finite `some E` branches of `scalarQChern` and `scalarP2Chern` and applies the explicit raw finite coefficient transport theorem. Added the corresponding DAG node and updated the assigned node's proof dependency to record this route.

## Proved and sorry left

The assigned theorem `AlgebraicGeometry.ProEtale.RationalP1.scalar_chern_base_change_chern_some` is proved. The new lower-level theorem `AlgebraicGeometry.ProEtale.RationalP1.scalar_chern_base_change_chern_some_raw` remains a split-off `sorry`, covering the concrete coefficient-level exchange mate and normalized Chern transport.

## No longer needed

No proof-dependency imports were removed. The assigned theorem uses only the raw finite coefficient transport node in addition to its public statement imports.

## Where the brief, the DAG or earlier work was wrong

The original node treated the finite coefficient specialization as a single opaque obligation. The Lean definitions expose a concrete integral-to-rational transport composite, so the obligation is reduced to that lower-level raw equation before the wrapper theorem.

## New nodes

`lem-sfb-rational-p1-scalar-chern-base-change-chern-some-raw` is added in `lean/Sheaf/Paper/RationalP1ScalarChernSomeRaw.lean`; its proof is the explicit finite coefficient exchange mate and endpoint normalization described in its docstring.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.RationalP1ScalarChernBaseChangeChernSome": "6518b7106de98c78792c366a0ec419d8a10a974f", "Sheaf.Paper.RationalP1ScalarChernSomeRaw": "623c292cd8ce51c7a0877fc33c2cde6fb25ec80c"}, "results": {}, "time": "2026-10-28T08:07:29+0800", "transitive": 0, "version": 1}
```

## Second reading by W9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
