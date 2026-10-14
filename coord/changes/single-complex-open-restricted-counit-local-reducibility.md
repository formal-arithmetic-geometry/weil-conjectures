# AlgebraicGeometry.singleComplexOpen_restricted_counit_cancellation

## Reason

Repair the returned single-file timeout (99 seconds in the global build, and over
60 seconds alone). Profiling exposed definitional equality checks expanding
Functor.mapHomotopyCategory into homological-complex components and ultimately
restriction of module-valued sheaves. Keep constructed functors abstract locally,
and allow implicit unification to unfold the scheme-module/category aliases.
A separate proved categorical helper removes the mapped identity before the final
comparison, avoiding speculative simplification of these concrete functor terms.

These attributes and elaboration options affect this file only. No definition body,
public signature, public import, global attribute, or target meaning changes.

## Old

The original file had the following file-level option and no local attributes:

```lean
set_option autoImplicit false
```

The theorem's complete original signature is preserved verbatim. The repository
version had `:= by sorry`; the returned sandbox already contained a categorical
cancellation proof but no report or node updates, and timed out.

## New

The definition reducibility used while elaborating this proof is now:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] derivedPullback singleComplexOpenPullbackIso
  Functor.mapHomotopyCategory Functor.mapDerivedCategory
  openPinnedHomotopyTensorRestrictionIso
attribute [local implicit_reducible] Scheme.Modules Scheme.Modules.Hom TopCat.Sheaf
  DerivedCategory HomotopyCategory
```

The theorem alone has `set_option linter.unusedVariables false in` to retain the
existing unused F₀ and a signature bindings, and `set_option maxHeartbeats 800000 in`
for the pinned-choice/instance comparisons. The wall-clock limit remains 60 seconds.
All added private lemmas are completely proved. The mapped identity is removed by
`remove_mapped_identity`, its equality is mapped through the remaining composite,
and transitivity combines it with `cancel_restriction_counit`. No new hole is added.

## Users

`tools/downstream.py --direct --uses singleComplexOpen_restricted_counit_cancellation`
identifies this sole direct importer and declaration caller:

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SingleComplexOpenPullbackCounitHomotopyFactorization | unclaimed | Existing statement, visibility, public imports, and definition reducibility seen by this importer remain identical. Its original source is checked against the repaired compiled module; no adaptation is needed. |

All transitive importers likewise see the same interface: the changed definition
attributes are local, and the new helpers are private. No importer source is delivered.
The returned message naming SingleComplexOpenRestrictedCounitCancellation as its
own importer is not a source import edge. Both the repaired item and its actual
importer are checked within the normal single-file limits.

## Status

landed 20261014T080626-L-3795474 2026-10-14 (merge of deliver/E2/Sheaf.AlgebraicGeometry.SingleComplexOpenRestrictedCounitCancellation)
