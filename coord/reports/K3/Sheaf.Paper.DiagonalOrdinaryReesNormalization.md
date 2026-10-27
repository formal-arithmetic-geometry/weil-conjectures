## What changed

Copied `Sheaf.Paper.DiagonalOrdinaryReesNormalization` into the sandbox and proved its
existential wrapper. The proof constructs the normalized diagonal section comparison with
`FiniteRingSectionDeformation.existsUnique_normalized`, constructs the Rees-to-symmetric-cone
pullback square from `coneBundleIso_spec` and `reesConeComparison_spec`, and applies the
fixed-witness equation in the new `Sheaf.Paper.DiagonalOrdinaryReesEquation` module.

## Proved and sorry left

Closed `WeilConjectures.PurityFiniteSetting.diagonalOrdinaryReesNormalization` (one
sorry closed). Added one strictly smaller sorry, named
`WeilConjectures.PurityFiniteSetting.diagonalOrdinaryReesEquation`, for the final
fixed-witness categorical equation.

## No longer needed

The proof does not use the previously listed proof dependencies
`lem-pur-diagonal-ordinary-orientation-rigidity`,
`lem-pur-diagonal-ordinary-orientation-normalization`,
`lem-sp-finite-section-integrated-specialization-base-change`, or
`lem-pur-chart-dnc-vector-factors`; their modules are not imported. The only retained
proof dependency is `lem-trf-finite-ring-section-deformation` for the normalized section
comparison and Rees/cone interfaces.

## Where the brief, the DAG or earlier work was wrong

The original node listed a full categorical construction as one step, but the available
interfaces reduce the assigned theorem to witness construction plus one fixed-witness
Rees equation. The latter is left as the new strictly smaller node above.

## New nodes

`lem-pur-diagonal-ordinary-rees-equation` — fixed κ and pullback square version of the
final Rees equation; its declaration is in
`lean/Sheaf/Paper/DiagonalOrdinaryReesEquation.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.DiagonalOrdinaryReesEquation": "5ef1c9275a9ac1f790840a41c961013103225265", "Sheaf.Paper.DiagonalOrdinaryReesNormalization": "29c9ccec5e22103e1e0aaed5f0eeb354a26f150c"}, "results": {}, "time": "2026-10-28T03:50:06+0800", "transitive": 0, "version": 1}
```

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
