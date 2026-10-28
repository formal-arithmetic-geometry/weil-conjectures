## What changed

Proved `WeilConjectures.integralDualizing_mapping_limit_hom_at` by applying the existing
global mapping-limit comparison and then transporting its component at `K` through the
new degree-zero extraction interface. The proof uses the supplied tower, coherent finite
identifications, and limit presentation only to obtain the global comparison isomorphism.
The new module `Sheaf.SixFunctors.IntegralDualizingMappingLimitHomAtDegreeZero` records the
remaining degree-zero passage as a separate named theorem.

## Proved and sorry left

Closed the one original hole:

- `WeilConjectures.integralDualizing_mapping_limit_hom_at`.

One strictly lower degree-zero extraction obligation remains:

- `WeilConjectures.integralDualizing_mapping_limit_hom_at_degree_zero` in
  `Sheaf.SixFunctors.IntegralDualizingMappingLimitHomAtDegreeZero` (`sorry`, node
  `lem-coef-integral-dualizing-mapping-limit-hom-at-degree-zero`).

Thus 1 of 1 original sorries was closed and 1 lower statement was split off. No definition
contains `sorry`.

## No longer needed

None. No imports, declarations, nodes, or modules were removed. The degree-zero module
imports only `IntegralDualizingRoosModel`, which supplies the types in its public statement;
the global comparison remains a private proof import of the assigned module.

## Where the brief, the DAG or earlier work was wrong

The prior route stopped at the global comparison and did not expose the fixed-object
component needed by the displayed Hom equivalence. The global theorem has a different
conclusion (an isomorphism of functors), while the fixed-object target requires its
zeroth-Hom extraction and the coefficient-point identification. This delivery makes that
missing boundary explicit rather than treating the functor isomorphism as definitionally
equal to the target. No statement or definition was changed.

## New nodes

- `lem-coef-integral-dualizing-mapping-limit-hom-at-degree-zero`, implemented by
  `Sheaf.SixFunctors.IntegralDualizingMappingLimitHomAtDegreeZero` and declaring
  `WeilConjectures.integralDualizing_mapping_limit_hom_at_degree_zero`. It is the
  degree-zero extraction from a supplied global comparison at a single constructible
  object; it omits the tower and presentation hypotheses and is the remaining lower proof
  obligation.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralDualizingMappingLimitHomAt": "c5cc643b1bab34925d2b65f5fdb6e043536861e6", "Sheaf.SixFunctors.IntegralDualizingMappingLimitHomAtDegreeZero": "2a58e20fdcb0f70638c16d6f08e2fb15ee608850"}, "results": {}, "time": "2026-10-28T08:31:05+0800", "transitive": 0, "version": 1}
```

## Second reading by U5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
