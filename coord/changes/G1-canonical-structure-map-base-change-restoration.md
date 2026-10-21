# canonical_structure_map_base_change

## Reason

Restore the assigned rework module from the quarantine recorded in coord/rework.tsv.
Its live lean/ path is absent; the archive and its Lean/DAG attachment remain the
starting point. Retain its public theorem and the pinned derived functors, arbitrary
commutative square, structure-sheaf maps and universes exactly as stated.

The archived private naturality proofs alone take 53.5 seconds to compile. Profiling
finds repeated rewrites through the selected left-derived counit, homotopy quotient
and single-complex comparisons. Replace the pullback naturality proof by composition
of three naturality squares: the derived counit square; the localized single-complex
comparison square; and the single of the tensor-to-ordinary adjunction comparison
square. Two fully proved private category helpers perform the composition and map
an equality through a functor. The final identification is definitional. Scope
transparency-respecting elaboration to this helper so it keeps the existing functors
behind their interfaces. No definition, mathematical hypothesis, public import,
public signature, target statement or adopted source module is changed.

The main theorem still uses canonicalSingleBaseChangeComparison, naturality of both
single-module maps, and the unit clause of moduleBaseChangeMap_algebra. It does not
introduce a replacement obligation or select any new data. The actual restored
module compiles through lcompile.py in 15.8 seconds without errors or warnings.

## Old

The live module is absent. The preserved source is
quarantine/Sheaf/AlgebraicGeometry/CanonicalStructureMapBaseChange.lean.
Its theorem signature is:

```lean
theorem canonical_structure_map_base_change
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g) :
    (derivedPullback g).map
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map
            (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
          Scheme.Modules.canonicalSingleDirectImageMap f
            (SheafOfModules.unit X.ringCatSheaf)) ≫
      (schemeDerivedBaseChangeMap f f' g p h
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
            (SheafOfModules.unit X.ringCatSheaf)) ≫
        (schemeDerivedDirectImage f').map
          (Scheme.Modules.canonicalSinglePullbackMap p
              (SheafOfModules.unit X.ringCatSheaf) ≫
            (DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).map
                (SheafOfModules.pullbackObjUnitToUnit p.toRingCatSheafHom))) =
    (Scheme.Modules.canonicalSinglePullbackMap g (SheafOfModules.unit S.ringCatSheaf) ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0).map
            (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom)) ≫
      ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0).map
            (SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom) ≫
        Scheme.Modules.canonicalSingleDirectImageMap f'
          (SheafOfModules.unit X'.ringCatSheaf))
```

## New

Restore lean/Sheaf/AlgebraicGeometry/CanonicalStructureMapBaseChange.lean with
exactly the same public signature:

```lean
theorem canonical_structure_map_base_change
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g) :
    (derivedPullback g).map
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map
            (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
          Scheme.Modules.canonicalSingleDirectImageMap f
            (SheafOfModules.unit X.ringCatSheaf)) ≫
      (schemeDerivedBaseChangeMap f f' g p h
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
            (SheafOfModules.unit X.ringCatSheaf)) ≫
        (schemeDerivedDirectImage f').map
          (Scheme.Modules.canonicalSinglePullbackMap p
              (SheafOfModules.unit X.ringCatSheaf) ≫
            (DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).map
                (SheafOfModules.pullbackObjUnitToUnit p.toRingCatSheafHom))) =
    (Scheme.Modules.canonicalSinglePullbackMap g (SheafOfModules.unit S.ringCatSheaf) ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0).map
            (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom)) ≫
      ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0).map
            (SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom) ≫
        Scheme.Modules.canonicalSingleDirectImageMap f'
          (SheafOfModules.unit X'.ringCatSheaf))
```

## Users

The source-only downstream.py query reports an unknown module because the item is
quarantined; the --allow-missing query finds zero live importers. A search of both
lean/ and quarantine/ for the import and declaration, and of all DAG dependency
fields, finds the one quarantined parent below. Its proof uses the exact original
identity. Its obligation and dependency edges are retained; no adaptation is needed.
The unit sk-prop-av-cube has no realized entry bypassed by this restoration.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CanonicalStructureMapBaseChange | G1 | Restore the complete theorem; optimize a private naturality proof. |
| Sheaf.AlgebraicGeometry.FlatDerivedStructureUnitProperties | unclaimed | Quarantined parent; the same structure-map equation remains available. |

## Status

landed 20261021T002138-L-1491602 2026-10-21 (merge of deliver/G1/Sheaf.AlgebraicGeometry.CanonicalStructureMapBaseChange)
