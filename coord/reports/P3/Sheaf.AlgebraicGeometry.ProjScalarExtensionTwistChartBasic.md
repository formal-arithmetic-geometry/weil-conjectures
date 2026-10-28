## What changed

Added `ProjScalarExtensionTwistChartInjective` and
`ProjScalarExtensionTwistChartSurjective`, each stating one strict half of the
complete standard-chart comparison. Change record `coord/changes/proj-scalar-extension-twist-chart-basic.md` records the interface addition. The assigned theorem now proves bijectivity by
applying those two component theorems. Added the corresponding DAG nodes and updated
the assigned node's proof route to record the decomposition. The target signature is
unchanged.

## Proved and sorry left

The assigned declaration `scalarExtension_twistMap_chart_bijective` is proved by the
real constructor `⟨injective, surjective⟩`. Two component holes remain:
`scalarExtension_twistMap_chart_injective` and
`scalarExtension_twistMap_chart_surjective`. They are strictly simpler conclusions,
with the same hypotheses and chart map, and are named public statements with source
and proof plans in their docstrings and DAG nodes.

## No longer needed

The assigned module no longer directly imports the six proof-only modules for
homogeneous localization, graded localization, affine pullback sections, graded
module sheaves, tilde, and single-twist fractions; those imports remain in each
component module where the deferred component proofs will use them. No dependency
node is pruned from the component proof plans.

## Where the brief, the DAG or earlier work was wrong

The original one-step Lean proof plan did not expose a usable theorem combining the
five existential chart identifications, so the target could not be proved directly
from the available interfaces in this session. The route is therefore decomposed into
the mathematically independent injectivity and surjectivity chart arguments. The
statement and all target hypotheses remain unchanged.

## New nodes

- `lem-sfb-proj-scalar-extension-twist-chart-injective`
- `lem-sfb-proj-scalar-extension-twist-chart-surjective`

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistChartBasic": "5037cd18cc8644b6c787b9c150b645dfc264b7ef", "Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistChartInjective": "0419a4297c94c9704e719d91ba71b2c49de5c9d3", "Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistChartSurjective": "9a612c38a499e3b03e965919c75648d0757fbad6"}, "results": {"Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistChart": {"hash": "5f4d1dbfd56e68cd2272f1f4a94bbb3b075f3f24", "status": "OK"}}, "seconds": 11, "time": "2026-10-28T08:06:44+0800", "transitive": 0, "version": 1}
```

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
