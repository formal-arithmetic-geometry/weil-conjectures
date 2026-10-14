# AlgebraicGeometry.standardSingle_open_relative_arrow

## Reason

The item supplied by the dispatcher existed in the initial checkout, but the
fresh upstream base fetched during deliver3.py's first dry run removed its
module and DAG node. The delivery now reintroduces that exact supplied signature
with a proved reduction, plus the strictly smaller normalized coefficient lemma.
No existing target or consumer signature is changed. The reader must check
whether the upstream removal already pruned this item from the target route.

## Old

The module and node are absent from the fetched base. The supplied declaration
before its removal had the following exact signature:

```lean
theorem standardSingle_open_relative_arrow {Y B A : Scheme.{u}} (p : Y ⟶ B) (g : A ⟶ B) (W Z : Y.Opens) (hZ : Z ≤ W) (N : W.toScheme.Modules) : letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard (SheafOfModules.{u} (moduleRings X.toRingedSpace)) let f := W.ι ≫ p let K := (DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) 0).obj N let K' := (DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) 0).obj (Scheme.Modules.tensorPullbackObj (pullback.fst f g) N) Nonempty (relativeMVLocalArrow f (pullback.snd f g) g (pullback.fst f g) (IsPullback.of_hasPullback f g) K K' (Scheme.picardTermwiseSingleMap (pullback.fst f g) N) (W.ι ⁻¹ᵁ Z) ≅ Arrow.mk (standardSingleBaseChangeMap (Z.ι ≫ p) (Scheme.Modules.tensorPullbackObj (Y.homOfLE hZ) N) g))
```

## New

The supplied signature is preserved:

```lean
theorem standardSingle_open_relative_arrow {Y B A : Scheme.{u}} (p : Y ⟶ B) (g : A ⟶ B) (W Z : Y.Opens) (hZ : Z ≤ W) (N : W.toScheme.Modules) : letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard (SheafOfModules.{u} (moduleRings X.toRingedSpace)) let f := W.ι ≫ p let K := (DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) 0).obj N let K' := (DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) 0).obj (Scheme.Modules.tensorPullbackObj (pullback.fst f g) N) Nonempty (relativeMVLocalArrow f (pullback.snd f g) g (pullback.fst f g) (IsPullback.of_hasPullback f g) K K' (Scheme.picardTermwiseSingleMap (pullback.fst f g) N) (W.ι ⁻¹ᵁ Z) ≅ Arrow.mk (standardSingleBaseChangeMap (Z.ι ≫ p) (Scheme.Modules.tensorPullbackObj (Y.homOfLE hZ) N) g))
```

Its proof constructs the scheme and coefficient isomorphisms and applies the
proved source-coordinate conjugacy theorem. One lower coefficient identity is
split into `Sheaf.AlgebraicGeometry.SingleOpenTensorCoefficientCoherence`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StandardSingleOpenRelativeArrow | V4 | reintroduced with the supplied signature and a complete Lean reduction |

The current-base downstream.py query reports "unknown module" because the module
was removed. No existing module is adapted and no existing importer is changed.

## Status

landed 20261014T034914-L-816221 2026-10-14 (merge of deliver/V4/Sheaf.AlgebraicGeometry.StandardSingleOpenRelativeArrow)
