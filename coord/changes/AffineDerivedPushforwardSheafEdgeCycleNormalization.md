# AlgebraicGeometry.affineDerivedPushforwardSheafEdge_compatibility

## Reason

The arbitrary edge transformation was unconstrained. In particular the zero edge
chosen by the existing Nonempty theorem cannot agree with a nonzero derived unit.
The component helper repeats the same false universal statement, rather than
being a strictly smaller step. This repair formalizes the cycle cancellation step
for a cycle-normalized edge, and reopens the original normalized-existence theorem.
The unit sk-thm-picard-semicon has no realization by this auxiliary node; its route
and all Challenge signatures stay identical. This is a correction, not net proof
progress. The repaired conditional compatibility proof has no sorry dependency.

## Old

```lean
theorem affineDerivedPushforwardSheafEdge_compatibility
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ) :
  (ε : (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
      DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i ⋙
      RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom ⟶
    (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
      schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ)) ⋙
      DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i) →
    ∀ (F : ModuleCat.{u} A ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
      [F.Additive] [F.PreservesZeroMorphisms] [F.PreservesHomology]
      [(F ⋙ RingedSpace.moduleDirectImage
        (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).PreservesZeroMorphisms]
      [(F ⋙ RingedSpace.moduleDirectImage
        (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).PreservesHomology]
      (_hF : ∀ M, (F.obj M).IsQuasicoherent)
      (C : CochainComplex (ModuleCat.{u} A) ℤ)
      (hC : schemeDerivedQCohProperty (Spec (.of A))
        (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj C))),
      (RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).map
          (((C.sc i).mapHomologyIso F).inv ≫
            ((DerivedCategory.homologyFunctorFactors _ i).app
              ((F.mapHomologicalComplex (.up ℤ)).obj C)).inv) ≫
        ε.app ⟨_, hC⟩ =
      ((C.sc i).mapHomologyIso
        (F ⋙ RingedSpace.moduleDirectImage
          (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom)).inv ≫
        ((DerivedCategory.homologyFunctorFactors _ i).app
          (((F ⋙ RingedSpace.moduleDirectImage
            (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom)
              |>.mapHomologicalComplex (.up ℤ)).obj C)).inv ≫
        (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i).map
          (((RingedSpace.moduleDirectImage
            (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).rightDerivedFunctorUnit).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj
              ((F.mapHomologicalComplex (.up ℤ)).obj C)))
```

## New

```lean
theorem affineDerivedPushforwardSheafEdge_compatibility
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ) :
  (ε : (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
      DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i ⋙
      RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom ⟶
    (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
      schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ)) ⋙
      DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i) →
    (∀ (K : CochainComplex
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
      (hK : schemeDerivedQCohProperty (Spec (.of A)) (DerivedCategory.Q.obj K))
      (T : (K.sc i).LeftHomologyData)
      (U : ((((RingedSpace.moduleDirectImage
        (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).mapHomologicalComplex
          (.up ℤ)).obj K).sc i).LeftHomologyData)
      (k : (RingedSpace.moduleDirectImage
        (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).obj T.K ⟶ U.K),
      (RingedSpace.moduleDirectImage
        (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).map T.i = k ≫ U.i →
      (RingedSpace.moduleDirectImage
        (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).map
        (T.π ≫ T.homologyIso.inv ≫
          ((DerivedCategory.homologyFunctorFactors _ i).app K).inv) ≫ ε.app ⟨_, hK⟩ =
      k ≫ U.π ≫ U.homologyIso.inv ≫
        ((DerivedCategory.homologyFunctorFactors _ i).app
          (((RingedSpace.moduleDirectImage
            (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).mapHomologicalComplex
              (.up ℤ)).obj K)).inv ≫
        (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i).map
          (((RingedSpace.moduleDirectImage
            (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).rightDerivedFunctorUnit).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj K))) →
    ∀ (F : ModuleCat.{u} A ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
      [F.Additive] [F.PreservesZeroMorphisms] [F.PreservesHomology]
      [(F ⋙ RingedSpace.moduleDirectImage
        (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).PreservesZeroMorphisms]
      [(F ⋙ RingedSpace.moduleDirectImage
        (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).PreservesHomology]
      (_hF : ∀ M, (F.obj M).IsQuasicoherent)
      (C : CochainComplex (ModuleCat.{u} A) ℤ)
      (hC : schemeDerivedQCohProperty (Spec (.of A))
        (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj C))),
      (RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).map
          (((C.sc i).mapHomologyIso F).inv ≫
            ((DerivedCategory.homologyFunctorFactors _ i).app
              ((F.mapHomologicalComplex (.up ℤ)).obj C)).inv) ≫
        ε.app ⟨_, hC⟩ =
      ((C.sc i).mapHomologyIso
        (F ⋙ RingedSpace.moduleDirectImage
          (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom)).inv ≫
        ((DerivedCategory.homologyFunctorFactors _ i).app
          (((F ⋙ RingedSpace.moduleDirectImage
            (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom)
              |>.mapHomologicalComplex (.up ℤ)).obj C)).inv ≫
        (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i).map
          (((RingedSpace.moduleDirectImage
            (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).rightDerivedFunctorUnit).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj
              ((F.mapHomologicalComplex (.up ℤ)).obj C)))
```

## Users

`tools/downstream.py --uses affineDerivedPushforwardSheafEdge_compatibility`
finds only the item and the parent as declaration users. The 1,415 transitive
importers see the parent's identical existential statement; none of their
statements or definitions is weakened. No Challenge declaration changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdgeCompatibility | G4 | normalized-cycle premise added; conclusion unchanged; proved by cancelling an epi |
| Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdge | unclaimed in local claims snapshot | forced proof-only adaptation; original caller lacks the required normalization; same signature and visibility; restore its documented unresolved proof with sorry |

The adapted parent changes only its final proof (lines 88-90 of the original):
`obtain` of an arbitrary transformation and the invalid compatibility application
are replaced by `:= by sorry`. Its complete sourced proof docstring and node
lem-pc-affine-derived-pushforward-sheaf-edge already describe the actual remaining
construction. Imports are retained to keep the unheld adaptation minimal. The
original compiler failure is recorded under Forced adaptations in report.md.

## Status

landed 20261014T025138-L-156560 2026-10-14 (merge of deliver/G4/Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdgeCompatibility)
