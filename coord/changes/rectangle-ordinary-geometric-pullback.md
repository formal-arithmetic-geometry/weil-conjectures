# AlgebraicGeometry.rectangle_ordinary_geometric_pullback

## Reason

The quarantined rework source imported `Sheaf.AlgebraicGeometry.DerivedPullbackComposition`,
which is now a withdrawn empty module. The adopted source library provides the same pinned
composition declaration in `WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition`.
The proof import is redirected there. The quarantined file also set a local irreducibility
attribute on `derivedPullback`; the adopted definition is already irreducible, so that
redundant command is removed. The theorem statement and its mathematical content are
unchanged.

## Old

```lean
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition

attribute [local irreducible] derivedPullback

theorem rectangle_ordinary_geometric_pullback
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y S T : Scheme.{u}}
    (f : X ⟶ Y) (g : S ⟶ Y) (h : T ⟶ S)
    (k : pullback (pullback.snd f g) h ⟶ pullback f (h ≫ g))
    (hk₁ : k ≫ pullback.fst f (h ≫ g) =
      pullback.fst (pullback.snd f g) h ≫ pullback.fst f g)
    (hk₂ : k ≫ pullback.snd f (h ≫ g) = pullback.snd (pullback.snd f g) h) :
    let U := qcPullback (pullback.fst f (h ≫ g))
    let L := qcPullback k
    let V := qcPullback (pullback.fst f g) ⋙
      qcPullback (pullback.fst (pullback.snd f g) h)
    ∃ (s : U ⋙ L ≅ V),
      L.IsEquivalence ∧
      (∀ E : schemeDerivedQCohCategory X,
        (schemeDerivedQCohProperty (pullback (pullback.snd f g) h)).ι.map
            (s.hom.app E) =
          (let comp := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
            (Classical.choose_spec exists_derivedPullbackComposition)))
           (comp k (pullback.fst f (h ≫ g))).hom.app E.obj ≫
             eqToHom (congrArg (fun v ↦ (derivedPullback v).obj E.obj) hk₁) ≫
             (comp (pullback.fst (pullback.snd f g) h)
               (pullback.fst f g)).inv.app E.obj))
```

## New

```lean
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition

-- The adopted derived-pullback definition is already irreducible.

theorem rectangle_ordinary_geometric_pullback
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y S T : Scheme.{u}}
    (f : X ⟶ Y) (g : S ⟶ Y) (h : T ⟶ S)
    (k : pullback (pullback.snd f g) h ⟶ pullback f (h ≫ g))
    (hk₁ : k ≫ pullback.fst f (h ≫ g) =
      pullback.fst (pullback.snd f g) h ≫ pullback.fst f g)
    (hk₂ : k ≫ pullback.snd f (h ≫ g) = pullback.snd (pullback.snd f g) h) :
    let U := qcPullback (pullback.fst f (h ≫ g))
    let L := qcPullback k
    let V := qcPullback (pullback.fst f g) ⋙
      qcPullback (pullback.fst (pullback.snd f g) h)
    ∃ (s : U ⋙ L ≅ V),
      L.IsEquivalence ∧
      (∀ E : schemeDerivedQCohCategory X,
        (schemeDerivedQCohProperty (pullback (pullback.snd f g) h)).ι.map
            (s.hom.app E) =
          (let comp := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
            (Classical.choose_spec exists_derivedPullbackComposition)))
           (comp k (pullback.fst f (h ≫ g))).hom.app E.obj ≫
             eqToHom (congrArg (fun v ↦ (derivedPullback v).obj E.obj) hk₁) ≫
             (comp (pullback.fst (pullback.snd f g) h)
               (pullback.fst f g)).inv.app E.obj))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| (none) | — | No current module imports the quarantined Sheaf attachment. |

## Status

landed 20261020T174723-L-784854 2026-10-20 (merge of deliver/B5/Sheaf.AlgebraicGeometry.RectangleOrdinaryGeometricPullback)
