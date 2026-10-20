# AlgebraicGeometry.exists_affinePushforwardCohomologyEdge_identity

## Reason

Restore the quarantined module by using the proved adopted upstream declaration of
this same theorem. The archived module fails during import: the old Sheaf dependency
loads `AlgebraicGeometry.affineDerivedCohomologyModules` after the canonical upstream
module has already declared it. The upstream identity-edge module has the same proof,
with six explicit `SheafOfModules.{u}` annotations and the canonical upstream
factorization import. Its statement uses exactly the intended cohomology coordinates.

The restored module publicly re-exports this canonical provider at the existing import
path. Its DAG attachment moves to the provider, retaining all three proof steps and all
proof dependencies. This is duplicate consolidation and import repair; the archived
mathematics is preserved. No adopted source declaration or target changes.

## Old

The archived module publicly imports
`WeilConjectures.Algebra.Homology.AffinePushforwardComparisonCoordinates` and privately
imports `WeilConjectures.Algebra.Homology.AffineDerivedPushforwardSheafEdge` and
`Sheaf.Algebra.Homology.AffinePushforwardComparisonFactorization`. It declares:

```lean
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules (moduleRings Y.toRingedSpace))]

theorem exists_affinePushforwardCohomologyEdge_identity
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ)
    (σ : ModuleCat.restrictScalars φ ⋙ affinePushforwardTilde B ≅
      affinePushforwardTilde A ⋙
        Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom φ))) :
  ∃ α : affineDerivedCohomologyModules A i ⋙
      (ModuleCat.restrictScalars φ ⋙ affinePushforwardTilde B) ⟶
    (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
      schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ)) ⋙
      DerivedCategory.homologyFunctor
        (SheafOfModules (moduleRings (Spec (.of B)).toRingedSpace)) i,
    ∀ (C : CochainComplex (ModuleCat A) ℤ)
      (hK : schemeDerivedQCohProperty (Spec (.of A))
        (DerivedCategory.Q.obj (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj C))),
      affinePushforwardCohomologyMapOfComparison A B φ σ C i ≫
        (DerivedCategory.homologyFunctor
          (SheafOfModules (moduleRings (Spec (.of B)).toRingedSpace)) i).map
          ((schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ))).map
            (𝟙 _)) =
        (affinePushforwardTilde B).map ((ModuleCat.restrictScalars φ).map
          (affinePushforwardRepresentativeCohomologyIso A C _ (Iso.refl _) i).hom) ≫
          α.app ⟨_, hK⟩
```

## New

The restored module contains this public re-export and declares no duplicate theorem:

```lean
public import WeilConjectures.Algebra.Homology.AffinePushforwardCohomologyEdgeIdentity
```

That existing module provides the following signature with the same hypotheses and
conclusion, making the sheaf universe explicit as required by the coordinate definitions:

```lean
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

theorem exists_affinePushforwardCohomologyEdge_identity
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ)
    (σ : ModuleCat.restrictScalars φ ⋙ affinePushforwardTilde B ≅
      affinePushforwardTilde A ⋙
        Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom φ))) :
  ∃ α : affineDerivedCohomologyModules A i ⋙
      (ModuleCat.restrictScalars φ ⋙ affinePushforwardTilde B) ⟶
    (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
      schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ)) ⋙
      DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i,
    ∀ (C : CochainComplex (ModuleCat A) ℤ)
      (hK : schemeDerivedQCohProperty (Spec (.of A))
        (DerivedCategory.Q.obj (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj C))),
      affinePushforwardCohomologyMapOfComparison A B φ σ C i ≫
        (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i).map
          ((schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ))).map
            (𝟙 _)) =
        (affinePushforwardTilde B).map ((ModuleCat.restrictScalars φ).map
          (affinePushforwardRepresentativeCohomologyIso A C _ (Iso.refl _) i).hom) ≫
          α.app ⟨_, hK⟩
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.AffinePushforwardCohomologyEdgeIdentity | P1 | Restore the import path as a public re-export of the proved upstream theorem. |
| WeilConjectures.Algebra.Homology.AffinePushforwardCohomologyEdgeIdentity | unclaimed | Canonical provider, read only; no adaptation. |
| WeilConjectures.Algebra.Homology.AffinePushforwardCohomologyEdgeExists | unclaimed | Existing direct theorem consumer imports the upstream provider already; no adaptation. Its original argument is checked through the restored path in scratch. |

`tools/downstream.py` with `--allow-missing --uses` reports zero downstream modules
for the quarantined path. Searching both active and quarantined Lean sources finds no
importer of that path; the upstream edge-existence module is the sole direct user of
the theorem. The root `WeilConjectures` aggregate imports the upstream provider.
DAG searches find no parent citing this node as a dependency; the parent edge-existence
node is already attached to the upstream theorem that uses this result. All of the
identity node's dependencies are preserved. No consumer, definition or target statement
is weakened, and no consumer source requires an edit.

## Status

landed 20261020T160759-L-3407880 2026-10-20 (merge of deliver/P1/Sheaf.Algebra.Homology.AffinePushforwardCohomologyEdgeIdentity)
