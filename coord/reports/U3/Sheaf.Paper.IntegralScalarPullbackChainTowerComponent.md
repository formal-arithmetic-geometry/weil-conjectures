## What changed

Proved `WeilConjectures.integralScalarPullbackChainTower_f` in the assigned module.
The finite-level proof identifies the composite by its existing generator
normalization, and the tower proof assembles the level identities. A proved
private helper establishes composition compatibility of the additive Roos comparison.
The final proof combines these identities and evaluates in the requested degree.
The finite and strict-tower composition lemmas are proved in two new modules,
`Sheaf.Paper.IntegralScalarPullbackLevelComposition` and
`Sheaf.Paper.IntegralScalarPullbackTowerComposition`. Both are used by the final
proof. All existing signatures and public imports are preserved. Additional imports expose
existing private proof APIs only inside this module.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.integralScalarPullbackChainTower_f`
(node `lem-pur-integral-scalar-pullback-chain-tower-component`).
Also proved `WeilConjectures.integralScalarPullbackLevelComposition` and
`WeilConjectures.integralScalarPullbackTowerComposition` in their new modules.
No holes added; no `sorry` remains in any delivered module. This is a proof, with
no split-off proof holes.

## No longer needed

None. Both original public imports and all declared mathematical dependencies are
used. The proof follows the existing generator, tower, and Roos-coordinate route.
No module or node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan was sound. Existing uniqueness of the finite-level
normalized comparison replaces a second adjunction/extensionality calculation.
The node now records the existing supporting proof APIs used explicitly by the
finite-generator and additive Roos calculations.
No statement or definition correction was necessary. No unit route was changed.

## New nodes

`lem-pur-integral-scalar-pullback-level-composition` records the proved finite-level
composition law, a genuine generator calculation before taking any inverse limit.
`lem-pur-integral-scalar-pullback-tower-composition` records the proved assembly of
that law over the strict reduction tower. Both follow the existing node's proof
plan and cite its sources. Searches found generic scalar/pullback associators,
while the existing specialized normalization and uniqueness lemmas prove exactly
the finite-level step needed here. The zero complex, empty site, level zero and
identity coefficient embeddings introduce no exception to either argument.

Profiling found expensive kernel conversions of the existing chosen functors.
Local irreducibility protects their data and local structural reduction attributes
avoid unnecessary elaborator unfolding. The accumulated file still exceeded 60 s,
so the two proved steps were moved to separate modules after those improvements,
without changing a shared definition or adding a proof hole.

All three delivered modules compile through `lcompile.py`: finite level 37.2 s,
strict tower 35.8 s, and the final component 39.7 s. No profiler options remain.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntegralScalarPullbackChainTowerComponent": "b3e88157ce0eddd1aff547a8bfa07ecc66176150", "Sheaf.Paper.IntegralScalarPullbackLevelComposition": "f612eec283e453ec2c3f16daff00b406e4755a05", "Sheaf.Paper.IntegralScalarPullbackTowerComposition": "143ddae4ee11e6a5a43143a11c8c4ab0d9f53528"}, "results": {"Sheaf.Paper.IntegralScalarPullbackChainTower": {"hash": "8cbfe392bd5c45c47f29d36c0d021c4c44d80fd3", "status": "OK"}}, "seconds": 15, "time": "2026-10-28T02:42:28+0800", "transitive": 0, "version": 1}
```

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
