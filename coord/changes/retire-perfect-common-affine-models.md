# AlgebraicGeometry.Scheme.perfect_common_affine_models

## Reason

Retire the duplicate `Sheaf.AlgebraicGeometry.PerfectCommonAffineModels`, as assigned in
`coord/retire-items.tsv`. The adopted upstream twin contains the complete theorem and both
private helpers. The only mathematical-code differences are explicit `overFunctor.{u}`
universe annotations upstream; all hypotheses and conclusions agree. No upstream file is edited.

## Old

In `Sheaf.AlgebraicGeometry.PerfectCommonAffineModels`:

```lean
theorem perfect_common_affine_models (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (E F : schemeDerivedCategory X) (hE : IsPerfect X E) (hF : IsPerfect X F) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧
      ∃ A B : CochainComplex
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ,
        IsStrictlyPerfect X U A ∧ IsStrictlyPerfect X U B ∧
        Nonempty ((SheafOfModules.overFunctor
          (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj A) ∧
        Nonempty ((SheafOfModules.overFunctor
          (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj F ≅
          DerivedCategory.Q.obj B)
```

The consumer imported `Sheaf.AlgebraicGeometry.PerfectCommonAffineModels` privately.

## New

Use the existing declaration in `WeilConjectures.AlgebraicGeometry.PerfectCommonAffineModels`:

```lean
theorem perfect_common_affine_models (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (E F : schemeDerivedCategory X) (hE : IsPerfect X E) (hF : IsPerfect X F) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧
      ∃ A B : CochainComplex
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ,
        IsStrictlyPerfect X U A ∧ IsStrictlyPerfect X U B ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj A) ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj F ≅
          DerivedCategory.Q.obj B)
```

The consumer imports the upstream twin privately. The Sheaf duplicate is withdrawn using
`deleted.txt`. The DAG attachment points to the upstream theorem, preserving its proof route.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PerfectDerivedTensor | unclaimed | Replace one private import; the existing theorem application and all signatures stay identical. |

`tools/downstream.py Sheaf.AlgebraicGeometry.PerfectCommonAffineModels --uses
perfect_common_affine_models` lists precisely this consumer, besides the declaration itself.
The retirement table also names LocalPerfectSupportedStabilization and PerfectTwoOutOfThree;
those Sheaf modules have already disappeared, and their upstream versions already import the twin.
No target statement or definition changes its meaning; no target review is reopened.

## Status

landed 20261020T135347-L-1813671 2026-10-20 (merge of deliver/A7/Sheaf.AlgebraicGeometry.PerfectCommonAffineModels)
