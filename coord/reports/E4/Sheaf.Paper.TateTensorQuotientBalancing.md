## What changed

The assigned theorem now combines two separate construction steps: existence of a morphism with the root-generator formula, and invertibility of any such morphism. It promotes the morphism with `asIso` and proves the full arbitrary-scalar formula by module linearity and a proved private scalar-balancing lemma for `pbcTensorSection`. The original statement and definitions are unchanged.

Added `Sheaf.Paper.TateTensorGeneratorMap` and `Sheaf.Paper.TateTensorGeneratorIsIso`. The former contains the concrete predicate `GeneratorCompatible` and the map-existence theorem; the latter contains the local rank-one invertibility theorem. Each is strictly a part of the original construction: the first asserts no inverse, and the second supplies no morphism.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Scheme.PurityIntegralTower.tateTensorQuotient_balancing` by a complete proof from the two new statements. Added two holes:

- `AlgebraicGeometry.Scheme.PurityIntegralTower.tateTensorQuotient_generator_map`, node `lem-pur-tate-tensor-generator-map`.
- `AlgebraicGeometry.Scheme.PurityIntegralTower.tateTensorQuotient_generator_isIso`, node `lem-pur-tate-tensor-generator-isiso`.

This is a decomposition, not a net proof of the original obligation. No sorry occurs in a definition. `GeneratorCompatible` is an explicit proposition, and no data is chosen from an unproved existence theorem in a definition.

## No longer needed

No imports or modules are pruned. The five original planned proof dependencies remain dependencies of the two construction steps. The assigned module imports only the construction API and its original public data module.

## Where the brief, the DAG or earlier work was wrong

The stated dependencies provide local root and coefficient structures but do not directly state the glued morphism with its required formula. Searching Mathlib and the source library found generic tensor scalar extension and root-coordinate lemmas, and finite coefficient comparisons, rather than this actual inverse-limit root projection. A scalar-one comparison is equivalent to the original obligation by linearity, so that prospective split was discarded. The delivered split separates existence of the normalized map from its local rank-one invertibility instead.

The empty scheme has the unique map and inverse; degree zero uses the coefficient unit. The construction statements impose neither nonemptiness nor extra primitive-root choices on the global scheme.

## New nodes

`lem-pur-tate-tensor-generator-map` records construction and gluing of the normalized root projection morphism. `lem-pur-tate-tensor-generator-isiso` records the local basis-to-basis argument proving invertibility of any such morphism. Each module includes its source and a full proof in words. The assigned node now records their combination and the proved scalar-balancing step. No existing interface was changed and no change record is needed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.TateTensorGeneratorIsIso": "10197fc0b382ae3b858336bdd67f7cd941c831fe", "Sheaf.Paper.TateTensorGeneratorMap": "b881bb4b2e1245bd70cd1f6ca02b6fd13543100b", "Sheaf.Paper.TateTensorQuotientBalancing": "a1e4ae52fff774e5b68c9708d7606a69df8ce797"}, "results": {"Sheaf.Paper.NormalizedTateTensorTowerCore": {"hash": "c9f24b8719d66395933946e611d53252b4b962db", "status": "OK"}}, "seconds": 87, "time": "2026-10-28T03:48:07+0800", "transitive": 0, "version": 1}
```

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
