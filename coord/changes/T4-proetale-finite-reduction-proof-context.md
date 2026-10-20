# ProEtaleFiniteReductionPullback proof context

## Reason

Stage-3 preflight classifies added context commands as a possible change to what
importers see and requires this record. The commands support the completed proof
without changing a public declaration, definition body, public import, notation or
existing global attribute. No target statement or definition changes meaning.

The extra universe is used only by the private locally-surjective extensionality
lemma. Local irreducibility prevents proof elaboration from expanding adjunction
and global-sections constructions. The point-unit identity is proved first for
abstract categories at the level of natural transformations, then specialized;
its component calculation avoids expensive conversion between concrete categories.

## Old

The original module has:

```lean
universe u
```

It has no local irreducibility commands or declaration-scoped backward
transparency settings. Its two public coefficient-comparison definitions and the
signature of `sfb_finite_reduction_pullback` are the reference versions retained
verbatim by this delivery.

## New

The universe command is:

```lean
universe u v
```

The added local attribute commands are:

```lean
attribute [local irreducible] upperStarLowerStarAdjunction constantSheafΓAdj
  globalSectionsLowerStarIso

attribute [local irreducible] pointUpperStarLowerStarAdjunction
```

The new private construction `directImageTransport` carries `@[irreducible]`.
It is the explicit composite of the equality isomorphism for direct image and the
inverse direct-image compositor. No existing public declaration gains an attribute.

Proof declarations also use one or both of these declaration-scoped commands:

```lean
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
```

Every such setting uses `in`. The local attributes end with the module's namespace
scope and do not change the attributes seen by importers. The two public definition
bodies, all three public signatures, and both public imports are unchanged.
Only private proved helpers, private proof imports and the theorem proof are added
or changed. No data is chosen from an undetermined existence statement.

## Users

Read-only `tools/downstream.py` reports 276 transitive importers. Its `--uses`
queries for `sfbConstantRingAbIso`, `sfbFiniteCoefficientPullbackIso` and
`sfb_finite_reduction_pullback` find exactly the two modules below. The consumer
source is unchanged; no forced adaptation or additional claim is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleFiniteReductionPullback | T4 | Completes the theorem with private proof helpers and local proof context. Public definitions and signatures are unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback | unclaimed (no current claim record) | Uses all three public declarations. Their definitions, signatures and visibility are preserved; no source edit. |

Validation: lcompile.py compiled the final item in 20.2 seconds and the unchanged
consumer source in 24.4 seconds against the same sandbox build, both without errors
or warnings. The temporary consumer copy is excluded from this delivery.

## Status

landed 20261020T211830-L-3508553 2026-10-20 (merge of deliver/T4/Sheaf.AlgebraicGeometry.ProEtaleFiniteReductionPullback)
