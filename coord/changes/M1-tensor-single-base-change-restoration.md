# tensorSingleBaseChangeSquare

## Reason

Restore the complete quarantined module named by coord/rework.tsv. The archived
statement fails to elaborate after the upstream sync: within Scheme.Modules,
unqualified derivedPullback resolves to the newer functor on DerivedCategory
S.Modules with morphisms in universe u. The selected counits and canonical
base-change map instead use AlgebraicGeometry.derivedPullback on the shared
derived categories with morphisms in arbitrary universe w. The compiler reports
Quiver.Hom.{u, u + 1} where Quiver.Hom.{w, u + 1} is required.

Qualify AlgebraicGeometry.derivedPullback.{u, w}, canonicalSingleDirectImageMap.{u, w},
and schemeDerivedDirectImage.{u, w, w} in the conclusion. These recover exactly the
pinned functors intended by the node, its chosen counits, and the ordinary
canonicalSingleBaseChangeComparison theorem. All binders, hypotheses, canonical
maps and the naturality/cancellation proof remain intact. No definition, adopted
source module, target statement, or unit route changes. The module compiles
without errors or warnings; #print axioms lists only propext, Classical.choice,
and Quot.sound. Archived and restored hole counts are both zero.

## Old

The lean/ path is absent; the original source is preserved at
quarantine/Sheaf/AlgebraicGeometry/Picard/TensorSingleBaseChangeSquare.lean.

```lean
theorem tensorSingleBaseChangeSquare
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' T : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ T)
    (g : T ⟶ S) (v : X' ⟶ X) (h : v ≫ f = f' ≫ g)
    [(tensorPullback g).Additive] [(tensorPullback v).Additive] (G : X.Modules) :
    let εg := (Classical.choose (Classical.choose_spec
      exists_derivedPullbackComposition.{u, w})) g
    let εv := (Classical.choose (Classical.choose_spec
      exists_derivedPullbackComposition.{u, w})) v
    let cg := εg.app ((HomotopyCategory.singleFunctor _ 0).obj ((pushforward f).obj G)) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex
          (tensorPullback g) (ComplexShape.up ℤ) 0).hom.app ((pushforward f).obj G)))
    let cv := εv.app ((HomotopyCategory.singleFunctor _ 0).obj G) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex
          (tensorPullback v) (ComplexShape.up ℤ) 0).hom.app G))
    cg ≫ (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0).map
          (moduleBaseChangeMap f f' g v h G) ≫
        canonicalSingleDirectImageMap f' ((tensorPullback v).obj G) =
      (derivedPullback g).map (canonicalSingleDirectImageMap f G) ≫
        schemeDerivedBaseChangeMap f f' g v h ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ≫
        (schemeDerivedDirectImage f').map cv
```

## New

```lean
theorem tensorSingleBaseChangeSquare
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' T : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ T)
    (g : T ⟶ S) (v : X' ⟶ X) (h : v ≫ f = f' ≫ g)
    [(tensorPullback g).Additive] [(tensorPullback v).Additive] (G : X.Modules) :
    let εg := (Classical.choose (Classical.choose_spec
      exists_derivedPullbackComposition.{u, w})) g
    let εv := (Classical.choose (Classical.choose_spec
      exists_derivedPullbackComposition.{u, w})) v
    let cg := εg.app ((HomotopyCategory.singleFunctor _ 0).obj ((pushforward f).obj G)) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex
          (tensorPullback g) (ComplexShape.up ℤ) 0).hom.app ((pushforward f).obj G)))
    let cv := εv.app ((HomotopyCategory.singleFunctor _ 0).obj G) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex
          (tensorPullback v) (ComplexShape.up ℤ) 0).hom.app G))
    cg ≫ (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0).map
          (moduleBaseChangeMap f f' g v h G) ≫
        canonicalSingleDirectImageMap f' ((tensorPullback v).obj G) =
      (AlgebraicGeometry.derivedPullback.{u, w} g).map
        (canonicalSingleDirectImageMap.{u, w} f G) ≫
        schemeDerivedBaseChangeMap f f' g v h ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ≫
        (schemeDerivedDirectImage.{u, w, w} f').map cv
```

## Users

The downstream.py query reports unknown module because the item is quarantined.
A scan of lean/, quarantine/ and DAG references finds one direct Lean consumer,
TensorDegreeZeroMateSquare, which is also quarantined. Its use applies the
arbitrary-square theorem to the fibre square and then maps it under H0; precisely
the same identity on the pinned shared derived category is supplied after this
repair. Its dependency edge is retained. No current lean/ consumer needs an
adaptation, and no consumer is removed or weakened. The quarantined parent's
independent restoration remains assigned through the existing rework machinery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Picard.TensorSingleBaseChangeSquare | M1 | Restore the complete proof with the pinned functor explicitly qualified. |
| Sheaf.AlgebraicGeometry.Picard.TensorDegreeZeroMateSquare | unclaimed | Quarantined parent; intended pinned identity unchanged; dependency retained. |

## Status

landed 20261021T004835-L-1793417 2026-10-21 (merge of deliver/M1/Sheaf.AlgebraicGeometry.Picard.TensorSingleBaseChangeSquare)
