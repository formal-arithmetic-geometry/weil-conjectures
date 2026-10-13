# AlgebraicGeometry.Scheme.picard_termwise_counit_composition

## Reason

The checker conservatively requires a record for section commands. This delivery
adds local reducibility attributes and declaration-scoped unification settings to
control the proof's comparisons between module-sheaf presentations and between
complexes and their homotopy classes. No exported definition, instance, notation,
or declaration signature changes. The 60-second file compilation limit is retained.

## Old

```lean
attribute [local instance] Functor.additive_of_preserves_binary_products

variable [∀ Y : Scheme.{v},
  HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
```

The existing theorem's unchanged signature was followed by `:= by sorry`.

## New

```lean
attribute [local instance] Functor.additive_of_preserves_binary_products

attribute [local irreducible] derivedPullback picardTermwiseCounit
  Modules.tensorPullbackCompositionIso
  Modules.tensorPullback Modules.tensorPullbackObj
attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] Modules.Hom DerivedCategory
  Functor.mapHomologicalComplex HomotopyCategory Functor.mapHomotopyCategory
  HomotopyCategory.quotient DerivedCategory.Q DerivedCategory.Qh
  HomologicalComplexUpToQuasiIso.Qh
```

The same instance-family variable command follows four underived private proved
helpers. The public theorem has these declaration-scoped settings:

```lean
set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
```

There are no new public declarations. The original public signature,
visibility, docstrings and public import are unchanged. The proof evaluates the pinned left-derived counit equation and cancels only
comparison isomorphisms.

## Users

The sole direct importer is listed below. No consumer needs adaptation because the
signature is unchanged and all attributes and settings are local.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PicardTermwiseCompositeCounitCore | V3 | Local proof environment only. |
| Sheaf.AlgebraicGeometry.PicardTermwiseCompositeCounit | not adapted | Applies the unchanged theorem. |

## Status

landed 20261013T201811-L-3977963 2026-10-13 (merge of deliver/V3/Sheaf.AlgebraicGeometry.PicardTermwiseCompositeCounitCore)
