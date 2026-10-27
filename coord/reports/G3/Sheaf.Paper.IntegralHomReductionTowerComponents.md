## What changed

The item theorem now has a complete Lean proof that combines two strictly smaller
intermediate statements. `reductionTower_components_transition` supplies the
component isomorphisms and the consecutive-transition square, while
`reductionTower_components_augmentation` supplies the augmentation equation for
any such transition-compatible family. The item imports these two proof modules;
the former direct proof-only imports of `IntegralHomModelsExist` and
`IntegralHomComparisonIsIso` were removed from the item module.

## Proved and sorry left

The declaration `WeilConjectures.IntegralHom.reductionTower_components` is
proved from the two intermediate declarations. Two strictly smaller obligations
remain as named theorems with `sorry`: 

- `WeilConjectures.IntegralHom.reductionTower_components_transition`, node
  `lem-sf-integral-hom-tower-components-transition`;
- `WeilConjectures.IntegralHom.reductionTower_components_augmentation`, node
  `lem-sf-integral-hom-tower-components-augmentation`.

No `sorry` occurs in a definition.

## No longer needed

The item proof no longer directly uses the nodes
`lem-sf-integral-hom-models-exist`, `lem-sf-integral-hom-comparison-is-iso`,
`lem-sfb-dc-hom-scalar-adjunction`, `def-pur-hom-complex`,
`def-pc-tensor-complex-sheaves`, or `def-sf-integral-hom-reduction-models` as
proof dependencies. The two split-off statements retain the project-specific
model and finite-comparison dependencies needed for their eventual proofs.

## Where the brief, the DAG or earlier work was wrong

The original node's proof plan describes the normalized tensor and quotient-unit
calculation but does not expose Lean declarations for the transition and
augmentation coherence steps. Those are independent substantial obligations, so
they are recorded as the two new nodes below rather than hidden in the parent
`sorry`.

## New nodes

`lem-sf-integral-hom-tower-components-transition` records the transition-square
part of the component comparison.

`lem-sf-integral-hom-tower-components-augmentation` records the augmentation
part after a transition-compatible family has been supplied.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntegralHomReductionTowerAugmentation": "5479ba3c01768401f954e78930328760b3543142", "Sheaf.Paper.IntegralHomReductionTowerComponents": "c4f13f51e55383d7c60b6a733c435e4012d834ac", "Sheaf.Paper.IntegralHomReductionTowerTransition": "42abd6e9edccbe9cf3f41102f67e0680350733e4"}, "results": {"Sheaf.Paper.IntegralHomAugmentedTowerComparison": {"hash": "b5ff6f5fbe78a46ff2f094fa4d9ff1572c1db394", "status": "OK"}}, "seconds": 12, "time": "2026-10-28T06:55:12+0800", "transitive": 0, "version": 1}
```

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
