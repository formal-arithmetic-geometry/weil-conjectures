## What changed

Filled `AlgebraicGeometry.ProEtale.SpTowerClasses.integralInverseSystem_abelian_comparison` in
`Sheaf.Paper.TowerIntegralAbelianComparison`. Private helpers construct the level comparison
by transposing the additive set-unit map, with its underlying map fixed by the canonical
sheaf-pullback/forget comparison. They make the Forget evaluation identifications natural
in both module morphisms and horizontal transitions, then assemble the ordinary system's
component comparisons into the required natural isomorphism of abelian towers.

Added private proof imports of `Sheaf.CategoryTheory.SheafPullbackForgetComparison` and
`Mathlib.CategoryTheory.Sites.CartesianMonoidal`. Existing statements and public imports
are unchanged. The item's DAG proof records the actual construction.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.SpTowerClasses.integralInverseSystem_abelian_comparison`
(node `lem-sp-tower-integral-abelian-comparison`). Added zero holes. No sorry remains in
any delivered declaration; no statement is split off. All private helpers are proved.

The addition argument uses generalized product sections and no nonzero-ring, nonempty-site
or invertibility assumption, so it includes zero coefficient rings and empty schemes.
The comparison chosen from its existence theorem is fixed by its underlying-set formula:
faithfulness determines the additive map and hence the entire isomorphism.

## No longer needed

No existing import is removed and no module is withdrawn. The proof does not use
`lem-sp-proetale-algebraic-inverse-image`
(`Sheaf.AlgebraicGeometry.ProEtaleAlgebraicInverseImage`): it uses the supplied algebraic
inverse-image data directly, without constructing a particular module inverse image.
It does not use `lem-sp-tower-forget-evaluation`
(`Sheaf.Paper.TowerForgetEvaluation`): the required natural evaluation comparison is
constructed directly from all four equations of the supplied Forget data, including
its morphism and horizontal-transition equations. Both nodes leave this node's proof
dependencies; they may still be needed elsewhere.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed. The original one-step plan needed an explicit
additive lifting argument, since `moduleUnderlying` compares sheaves of sets. The proof
supplies that argument using the module addition graph and the inverse-image adjunctions.
The Forget evaluation theorem alone does not assert naturality in systems or horizontal
compatibility, so these are verified explicitly rather than assumed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.TowerIntegralAbelianComparison": "32fdc62a81977eae904aea04d421521a5da50da6"}, "results": {"Sheaf.Paper.TowerIntegralInverseSystemNormalization": {"hash": "9fa9e6ac55a49e1909864da17dc81c22d7d7228d", "status": "OK"}}, "seconds": 69, "time": "2026-10-28T05:30:48+0800", "transitive": 0, "version": 1}
```

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
