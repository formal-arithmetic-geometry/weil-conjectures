# unboundedLeraySections: local transparency of rightDerivedFunctor

## Reason

The profiler reports repeated unfolding of `Functor.rightDerivedFunctor` into the
chosen Kan-extension colimit (`getColimitCocone` of the empty diagram) while
elaborating the existing Leray statement. This consumes 200000 heartbeats in the
statement and its restriction-square proof. A local irreducibility attribute keeps this
construction behind its existing derived-unit API. No public definition changes.

## Old

No local reducibility attributes on `Functor.rightDerivedFunctor`,
`Functor.rightDerivedFunctorUnit`, `Functor.rightDerivedFunctorCompUnit`, or
`Functor.rightDerivedFunctorNatTrans`.
The existing declarations, their signatures, and public imports are otherwise identical.

## New

Before the derived-unit proof helpers and the original theorem:

```lean
attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  Functor.rightDerivedFunctorCompUnit Functor.rightDerivedFunctorNatTrans
```

The attribute is local to this module. It changes no imported declaration body,
signature, or public attribute. The theorem retains its exact original signature. A theorem-local `maxHeartbeats 400000`
allows the normalized restriction-square elaboration across three independent derived-category
universes; the fixed 60-second per-file compilation limit is unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SpaceDerivedPushforwardUpperBound | unclaimed | No adaptation: the local attribute is not exported and the theorem's signature is unchanged. |
| Sheaf.AlgebraicGeometry.SpaceInverseModuleAffineBaseChange | unclaimed | No adaptation: the local attribute is not exported and the theorem's signature is unchanged. |
| Sheaf.Paper.SupportedImageTorsionReductionsCd | E1 | No adaptation: the local attribute is not exported and the theorem's signature is unchanged. |

## Status

landed 20261025T095200-L-3308632 2026-10-25 (merge of deliver/F2/Sheaf.CategoryTheory.Sites.UnboundedLeraySections)
