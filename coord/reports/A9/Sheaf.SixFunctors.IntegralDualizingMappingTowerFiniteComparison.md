## What changed

Repaired `WeilConjectures.integralDualizing_mapping_tower_finite_comparison` by importing
`Sheaf.SixFunctors.IntegralDualizingMappingTowerFiniteComponents`, obtaining its coherent
component comparison, and assembling it with `CategoryTheory.NatIso.ofComponents`.
Added the split-off module
`Sheaf.SixFunctors.IntegralDualizingMappingTowerFiniteComponents`, whose theorem records the
finite component isomorphisms and their naturality before assembly. Updated the assigned DAG
node's proof and proof dependencies to record this route.

## Proved and sorry left

Closed the assigned module's `integralDualizing_mapping_tower_finite_comparison` hole (1 of 1).
The new lower-level theorem
`integralDualizing_mapping_tower_finite_components` retains one `sorry`, with node
`lem-coef-integral-dualizing-mapping-tower-finite-components`; it is the finite-level
component construction and naturality step from the blueprint.

## No longer needed

No imports or declared proof dependencies were removed. The assigned module still needs
`Sheaf.SixFunctors.IntegralDualizingMappingTower`; the new component module uses the same
mapping-tower definitions. No existing DAG nodes became unnecessary.

## Where the brief, the DAG or earlier work was wrong

The assigned module's proof plan requires a coherent component construction that is not
provided by the published strict-tower definitions or by the existing finite comparison
lemmas. The prior `sorry` therefore cannot be discharged by a direct generic categorical
constructor alone. The missing construction is recorded as a strictly lower-level theorem;
the assigned theorem now contains the complete `NatIso.ofComponents` assembly.

## New nodes

`lem-coef-integral-dualizing-mapping-tower-finite-components` records the coherent family of
finite component isomorphisms and its naturality equation. Its source and proof steps follow
the finite reductions, exceptional adjunction, and exact tower evaluation steps of the
assigned node.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralDualizingMappingTowerFiniteComparison": "8bfae2307ef631cc72ec471be1af15844a114345", "Sheaf.SixFunctors.IntegralDualizingMappingTowerFiniteComponents": "f3f9def7332fcfe72c523eab8c154ee43ea6ba51"}, "results": {}, "time": "2026-10-28T09:40:22+0800", "transitive": 0, "version": 1}
```

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
