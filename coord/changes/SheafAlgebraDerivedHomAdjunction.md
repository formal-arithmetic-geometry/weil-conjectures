# Sheaf.AlgebraicGeometry.SheafAlgebraDerivedHomAdjunction

## Reason

Repair the returned equivalent-restatement split. The map-level derived adjunction is
now proved from a strictly smaller underived adjunction and an explicit localization
comparison. Remove the two unused proof imports identified by the reviewer.
All existing signatures and visibility remain unchanged.

## Old

```lean
theorem sheafAlgebraDerivedHom_adjunction
    (Y : Scheme.{u}) (B : Y.CommAlgebraSheaf) (hB : B.toModule.IsQuasicoherent)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wB} (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).obj B.right))] :
    Nonempty ((SheafOfModules.restrictScalars.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).map B.hom)).rightDerivedFunctor ⊣
          derivedRHomAlgebraModule Y B hB) := by sorry
```

The original target theorem had `:= by sorry`. The returned delivery replaced that
with transport of the admitted `sheafAlgebra_mapDerivedCategory_adjunction`.

## New

```lean
theorem sheafAlgebraDerivedHom_adjunction
    (Y : Scheme.{u}) (B : Y.CommAlgebraSheaf) (hB : B.toModule.IsQuasicoherent)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wB} (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).obj B.right))] :
    Nonempty ((SheafOfModules.restrictScalars.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).map B.hom)).rightDerivedFunctor ⊣
          derivedRHomAlgebraModule Y B hB) := by
  let F := SheafOfModules.restrictScalars.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).map B.hom)
  have : PreservesFiniteLimits F := sheafAlgebraRestrictScalars_preservesFiniteLimits Y B
  have : PreservesFiniteColimits F := sheafAlgebraRestrictScalars_preservesFiniteColimits Y B
  obtain ⟨adj⟩ := sheafAlgebra_mapDerivedCategory_adjunction Y B hB
  exact ⟨adj.ofNatIsoLeft F.rightDerivedFunctorIsoMapDerivedCategory.symm⟩
```

`sheafAlgebraDerivedHom_adjunction` transports the now-proved map-level adjunction.
`sheafAlgebra_mapDerivedCategory_adjunction` derives `sheafAlgebraHom_adjunction` and
constructs its right-functor comparison. The only admitted new theorem is the underived
adjunction, with its own module and node. The target removes the unused imports
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions` and
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.SheafAlgebraDerivedHomAdjunction | X3 | proof-only changes |
| Sheaf.AlgebraicGeometry.SheafAlgebraMapDerivedAdjunction | X3, new | now proved |
| Sheaf.AlgebraicGeometry.SheafAlgebraHomAdjunction | X3, new | underived obligation |

No existing public signature or definition changes; no forced adaptations.

## Status

landed 20261012T135336-L-1701452 2026-10-12 (merge of deliver/X3/Sheaf.AlgebraicGeometry.SheafAlgebraDerivedHomAdjunction)
