## What changed

The item theorem `WeilConjectures.integralDualizing_mapping_limit_hom` is now proved by
introducing an arbitrary constructible object `K` and applying the fixed-object comparison
from `Sheaf.SixFunctors.IntegralDualizingMappingLimitHomAt`.  The fixed-object comparison
is recorded as a new public theorem in its own module and is the remaining mathematical
obligation.

The item DAG node now records the fixed-object node as its proof dependency.  No existing
source-library module was changed.

## Proved and sorry left

Closed the item hole in `integralDualizing_mapping_limit_hom` (1 of 1 original sorries).

Added one split-off sorry in
`WeilConjectures.integralDualizing_mapping_limit_hom_at`, recorded by node
`lem-coef-integral-dualizing-mapping-limit-hom-at`.  It is the fixed-`K` component of the
mapping-limit comparison and is strictly below the universal statement proved in the item.

## No longer needed

None.  The original Roos-model import remains needed for the statement, and the new
fixed-object module is imported privately for the proof.

## Where the brief, the DAG or earlier work was wrong

The existing declarations expose the normalized tower, its coherent identifications, and
the Roos presentation, but no declaration supplies the finite-to-limit Hom comparison.
Consequently the displayed comparison cannot be proved from the current library without
the fixed-object intermediate theorem.  The universal statement is still exactly the
statement in the existing node.

## New nodes

`lem-coef-integral-dualizing-mapping-limit-hom-at` records the fixed-object degree-zero
mapping comparison and its source paragraph.  Its Lean declaration is
`WeilConjectures.integralDualizing_mapping_limit_hom_at` in
`lean/Sheaf/SixFunctors/IntegralDualizingMappingLimitHomAt.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralDualizingMappingLimitHom": "eae5138871de18abeb5e3d7802e0d08d95927e64", "Sheaf.SixFunctors.IntegralDualizingMappingLimitHomAt": "d3791c65e3cf9d849e1933ab94d2b95cf54af061"}, "results": {}, "time": "2026-10-28T06:43:25+0800", "transitive": 0, "version": 1}
```

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
