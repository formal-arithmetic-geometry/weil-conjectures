## What changed

Filled the two proof bodies in `Sheaf.Paper.CommonConstantUnitFrobenius`, retaining all
public signatures and definition bodies. Added private categorical transport lemmas.
The map formula uses the actual self-transition unit and the existing coefficient-unit
normalization theorem. The Frobenius equation is the inclusion of the existing rational
coherence equation, using the normalized common-stage compositor to identify the square.
The proof imports `Sheaf.Paper.CommonStagePullbackCoefficientUnit` and
`Sheaf.Paper.CommonStageCompositorIntegralNormalization`. Local reducibility settings
retain the abstractions of the large derived functors while reducing the lightweight
category wrappers.
The two existing DAG nodes now record those proof routes. The transport node prose is
corrected to its unchanged Lean attachment in
`coord/changes/J6-common-constant-unit-transport-node.md`.

Validation: remote single-file compilation succeeded in 30.6 seconds with no warnings.

## Proved and sorry left

Closed `WeilConjectures.ConstantPurityFrobenius.commonStageDerivedPullback_map_inclusion`
(node `lem-pur-common-constant-unit-frobenius-transport`) and
`WeilConjectures.ConstantPurityFrobenius.commonUnit_frobenius`
(node `lem-pur-common-constant-unit-frobenius`). Two local holes closed, zero holes added,
zero local holes remaining. The main proof uses the already stated
`WeilConjectures.ConstantPurityFrobenius.rationalizedUnit_frobenius`; its separate
rational-stage obligation stays with its existing node and module.

## No longer needed

No original imports were removed. The common-stage proof does not directly use
`lem-pur-proetale-constant-ring-composition` or
`lem-pur-completed-operation-tower-substitution`: finite and integral coherence are
handled by the existing rational-stage theorem. Their modules remain available to
other consumers; no withdrawal is requested. The transport lemma does not need
`lem-pur-common-constant-unit-frobenius-rational`: its map formula holds for arbitrary
schemes and included arrows, independently of Frobenius coherence. It also does not
use `def-weil-constant-weil-structure`, removed from that node's statement dependencies
when its prose was corrected to the existing general map formula.

## Where the brief, the DAG or earlier work was wrong

The old transport docstring described the self-stage comparisons as identity transports.
They retain nontrivial scalar unitors. Their coefficient-unit equations and naturality
cancel these unitors; treating them as definitionally identities would be incorrect.
The transport node's earlier proof concerned transport of the entire coherence equation;
its Lean attachment is the strictly smaller pullback-map formula. The updated node
statement and proof record the formula actually stated in Lean. Its public Lean
signature is unchanged;
there are no base DAG citers to adapt. The new main-node dependency uses exactly that formula.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 SLOW.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CommonConstantUnitFrobenius": "d70c4748d122fab4b25ed0bf466da0e380fdf9a8"}, "results": {"Sheaf.Paper.ConstantPurityFrobeniusSquare": {"hash": "57e1afb9cc6da75a28f05ec3856b5b1c77ee5d7b", "status": "SLOW"}}, "seconds": 139, "time": "2026-10-28T10:44:45+0800", "transitive": 0, "version": 1}
```

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
