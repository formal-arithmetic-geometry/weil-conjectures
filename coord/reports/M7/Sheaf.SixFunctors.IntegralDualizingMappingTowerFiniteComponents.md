## What changed

Replaced the hole in
`WeilConjectures.integralDualizing_mapping_tower_finite_components` by a complete
Lean combination of three distinct comparisons. The original signature and public
import are unchanged. The proof transports the finite dualizing identifications
through the quotient-system realization, proves their transition square by
cancelling `a m`, obtains the existing compactification pairing frame, and composes
the three natural isomorphisms. Their components and naturality give the original
conclusion.

The concrete intermediate functor `integralDualizingSupportSystemHom` is derived
quotient-system Hom from actual quotient-system compact support into the existing
base tensor unit, followed by integral scalar restriction and derived sections.
Its two definitions are literal composites of existing functors and contain no
choice from an unproved existence statement. In particular, no new copy of the
coefficient unit is defined.

This is a decomposition, not a closed proof of finite duality. The three remaining
statements separate actual mathematical operations: quotient-system realization
and scalar Hom, strict finite exceptional adjunction before any limit, and scalar
comparison for compact support without a dualizing tower. No supporting theorem
has the assigned theorem's hypotheses and conclusion under another name.

All five Lean modules compiled individually in import order. The first check took
6.2--10.4 seconds per file; subsequent checks cover the smaller public imports and
the reuse of the existing tensor unit. No existing module outside the assigned
module is changed. No target or source-library declaration is changed.

## Proved and sorry left

Closed the assigned hole:

- `WeilConjectures.integralDualizing_mapping_tower_finite_components`
  (`lem-coef-integral-dualizing-mapping-tower-finite-components`).

Added exactly three whole named theorem holes, each in a new module:

- `WeilConjectures.integralDualizing_mapping_tower_system_model`
  (`lem-coef-integral-dualizing-mapping-tower-system-model`). This asserts quotient
  realization and scalar Hom comparison for any normalized tower. It has no finite
  dualizing identifications or exceptional adjunction in its hypotheses or
  conclusion.
- `WeilConjectures.integralDualizing_system_finite_adjunction`
  (`lem-coef-integral-dualizing-system-finite-adjunction`). This is finite
  exceptional adjunction between two quotient-system Hom functors. Its conclusion
  contains neither an integral compact-support value nor an inverse limit.
- `WeilConjectures.integralDualizing_support_system_hom_comparison`
  (`lem-coef-integral-dualizing-support-system-hom-comparison`). This is scalar
  adjunction and compact-support reduction; it has no dualizing tower or finite
  exceptional input.

The item has zero holes; the delivery closes one and adds three. Thus the net hole
change is +2, a decomposition. Every new hole has a source, complete construction
in words in its docstring, and a matching DAG node. The zero input, zero tower and
empty scheme cases are included. Isomorphisms are natural before localization;
no naturality of an arbitrary objectwise family is asserted.

## No longer needed

No old import, module or mathematical dependency is pruned. The old direct proof
dependencies are distributed among the three new substeps, with ordinary internal
exceptional adjunction and the existing compactification models explicitly recorded. The
original public import remains unchanged. The new definition module imports only
`CoefTowerEvaluationPairingData`, which supplies its signatures.

The core uses the ordinary internal exceptional adjunction directly, rather than
`finiteMappingAdjunction`. A final DAG audit found that the latter has a long
proof-dependency route back to the assigned theorem; it is not an additional
dependency of this delivery. The ordinary adjunction and finite site comparison
are sufficient for the canonical projection/evaluation/counit transpose.

The proof does not use the disputed `coefTowerNaturalCurrying` theorem: its
arbitrary trace comparison does not specify preservation of the finite counits.
It remains an existing transitive public import of `IntegralDualizingMappingTower`,
so this delivery claims no pruning of it. Likewise the prior arbitrary-family
naturality split is not imported or used.

## Where the brief, the DAG or earlier work was wrong

The original one-hole node bundled scalar realization, finite exceptional
adjunction and compact-support scalar adjunction in one component-existence
claim. Its dependencies state those finite operations but do not directly give a
natural isomorphism between the two functors of this module. This delivery gives
the intermediate quotient-system functor explicitly and isolates these three
operations, rather than repeating the same component-existence claim.

The earlier U6 sandbox's naturality theorem quantified over an arbitrary family
of objectwise isomorphisms. That is not a valid naturality assertion: changing
components by unrelated automorphisms need not commute with an input morphism.
The present proof instead takes all components from one composite natural
isomorphism.

In the system-realization step, merely choosing finite K-injective complexes does
not automatically represent every semilinear transition by a chain map into the
chosen restricted target. The new proof in words uses successive roofs with a
quasi-isomorphism on the source instead. Since the index is a sequential quiver,
this constructs strict successor maps inductively; longer maps are composites.

The unit record `sk-prop-sf-biduality-general` has no realized statement or steps.
No unit or chapter record is changed; the prescribed finite-duality route remains.

## New nodes

`def-coef-integral-dualizing-support-system-hom` records the actual quotient-system
compact-support functor and its Hom into the already existing base tensor unit.

`lem-coef-integral-dualizing-mapping-tower-system-model` records quotient-system
realization and the natural scalar Hom comparison for a normalized tower.

`lem-coef-integral-dualizing-system-finite-adjunction` records the middle finite
exceptional adjunction, before any integral compact-support realization.

`lem-coef-integral-dualizing-support-system-hom-comparison` records the independent
compact-support reduction and scalar Hom comparison.

Blueprint and DAG searches found no exact existing statement for these concrete
intermediate functors. `CoefHomTowerScalarModel`,
`CoefPairingHomRepresentativeComparison`, `coefPairingCompactificationModels` and
`finiteMappingAdjunction` were checked. The first three provide prerequisite
models or evaluated comparisons, rather than natural isomorphisms with these
intermediate endpoints; the last is avoided for the DAG reason above. The
new nodes preserve the required scalar models, compactification models and ordinary
internal adjunction dependencies for the workers proving the substeps.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralDualizingMappingTowerFiniteComponents": "385694a7bd729b9dc1480773bff38db570167ea7", "Sheaf.SixFunctors.IntegralDualizingMappingTowerSystemModel": "9efea7437ca9379dc7590271f953b2c5449118ed", "Sheaf.SixFunctors.IntegralDualizingSupportSystemHom": "12ef1b0ddea1e67fcc5fde5ae9c42de4d135ee45", "Sheaf.SixFunctors.IntegralDualizingSupportSystemHomComparison": "ec3c9d3d4659bcc0908dacf852643b841e13bddc", "Sheaf.SixFunctors.IntegralDualizingSystemFiniteAdjunction": "0e64034ed4e4e071741ea9b290785e56b3a9fb46"}, "results": {}, "time": "2026-10-28T10:35:54+0800", "transitive": 0, "version": 1}
```

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
