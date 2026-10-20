# AlgebraicGeometry.Scheme.proEtaleUniverseLiftToOver

## Reason

The direct functor structure repeatedly unfolds the affine-colimit construction while elaborating the larger representability proof. The retained profiling attempt exceeded 60 seconds. Factor through the canonical scheme-universe-lift functor and Over.post, and mark this boundary irreducible. The wrapper lives in the new UniverseEnlargedEtaleRealization module, which is publicly imported because the definition body uses it. The object map and arrow map are the same; the new identity and composition proofs express the same functor laws. No theorem statement or mathematical meaning changes.

## Old

```lean
noncomputable def proEtaleUniverseLiftToOver (X : Scheme.{u}) :
    X.ProEt ⥤ Over (schemeUniverseLift.{u, u + 1} X) where
  obj U := Over.mk (schemeUniverseLiftMap.{u, u + 1} U.hom)
  map f := Over.homMk (schemeUniverseLiftMap.{u, u + 1} f.left) (by
    change schemeUniverseLiftMap.{u, u + 1} f.left ≫
      schemeUniverseLiftMap.{u, u + 1} _ = schemeUniverseLiftMap.{u, u + 1} _
    rw [← schemeUniverseLiftMap_comp]
    exact congrArg (schemeUniverseLiftMap.{u, u + 1}) f.w)
  map_id U := by
    apply Over.OverMorphism.ext
    change schemeUniverseLiftMap.{u, u + 1} (𝟙 U.left) = 𝟙 _
    let _ := schemeUniverseDiagram_hasColimit.{u, u + 1} U.left
    apply colimit.hom_ext
    intro j
    dsimp only [schemeUniverseLiftMap]
    rw [colimit.ι_desc]
    dsimp only [Cocone.whisker_ι, schemeUniverseLift]
    rw [Category.comp_id]
    change colimit.ι (schemeUniverseDiagram.{u, u + 1} U.left)
      ((CostructuredArrow.map (𝟙 U.left)).obj j) =
        colimit.ι (schemeUniverseDiagram.{u, u + 1} U.left) j
    let hj : j ⟶ (CostructuredArrow.map (𝟙 U.left)).obj j :=
      CostructuredArrow.homMk (𝟙 _) (by simp)
    have hw := colimit.w (schemeUniverseDiagram.{u, u + 1} U.left) hj
    change (schemeCoordinateRingLift.{u, u + 1}.op ⋙ Scheme.Spec).map (𝟙 j.left) ≫
      _ = _ at hw
    have hid := (schemeCoordinateRingLift.{u, u + 1}.op ⋙ Scheme.Spec).map_id j.left
    rw [hid, Category.id_comp] at hw
    exact hw
  map_comp f g := by
    apply Over.OverMorphism.ext
    change schemeUniverseLiftMap.{u, u + 1} (f.left ≫ g.left) =
      schemeUniverseLiftMap.{u, u + 1} f.left ≫ schemeUniverseLiftMap.{u, u + 1} g.left
    exact schemeUniverseLiftMap_comp f.left g.left
```

## New

```lean
@[irreducible]
noncomputable def proEtaleUniverseLiftToOver (X : Scheme.{u}) :
    X.ProEt ⥤ Over (schemeUniverseLift.{u, u + 1} X) :=
  ProEt.forget X ⋙ Over.post AlgebraicSpace.schemeUniverseLiftFunctor

```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ProEtaleLocalSystemRepresentability | F6 | Definition factored and its own proof unfolds the boundary explicitly. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | No source use of this helper; theorem signature and meaning preserved. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | No source use of this helper; theorem signature and meaning preserved. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | No source use of this helper; theorem signature and meaning preserved. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | No source use of this helper; theorem signature and meaning preserved. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | No source use of this helper; theorem signature and meaning preserved. |
| Sheaf.Paper.MiddleExtensionHcZero | E5 | No source use of this helper; theorem signature and meaning preserved. |
| Sheaf.Paper.NormalProEtaleMonodromy | K7 | No source use of this helper; theorem signature and meaning preserved. |
| Sheaf.Paper.SmoothLisseIntegralLattice | T8 | No source use of this helper; theorem signature and meaning preserved. |
| Sheaf.SecPurity.NormalLocallyConstantFiniteSection | P8 | No source use of this helper; theorem signature and meaning preserved. |

The downstream textual-use scan finds only the item itself mentioning this helper. The theorem still represents the same functor on every original object and arrow. No target uses a changed geometric construction: only its functor packaging changed.

## Status

landed 20261020T051244-L-1611405 2026-10-20 (merge of deliver/F6/Sheaf.AlgebraicGeometry.ProEtaleLocalSystemRepresentability)
