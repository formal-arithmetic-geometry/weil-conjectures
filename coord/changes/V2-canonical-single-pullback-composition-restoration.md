# AlgebraicGeometry.Scheme.Modules.canonicalSinglePullbackComposition

## Reason

Restore the quarantined zero-hole item against the adopted source interface.
`canonicalSinglePullbackMap` now explicitly uses
`AlgebraicGeometry.derivedPullback`, on the shared `schemeDerivedCategory` model.
Inside `AlgebraicGeometry.Scheme.Modules`, the newly imported same-namespace
`derivedPullback` denotes a different, standard-universe functor. Thus the old
unqualified spelling no longer elaborates for arbitrary `w`: the compiler reports
`Quiver.Hom.{u, u + 1}` where `Quiver.Hom.{w, u + 1}` is required. Qualifying the
intended functor restores the original mathematical statement and the pre-sync
elaborated type. No hypothesis, conclusion, universe parameter, or binder changes.
No definition or target statement changes.

The proof imports the adopted homotopy helper and the already proved counit
factorization. It replaces the broad final simplification with a private
comparison equation and generic proved categorical calculations. This avoids
expensive reduction of the chosen adjunctions. Local irreducibility annotations
for `tensorPullback` and `Adjunction.leftAdjointUniq`, and local notation
`dPullback`, apply only to elaborating this file. They export no attributes or
notation. Preflight conservatively requests this record because it sees the
qualified spelling and the local commands.

## Old

The quarantined signature (the unqualified functor was intended to denote
`AlgebraicGeometry.derivedPullback`):

```lean
theorem canonicalSinglePullbackComposition
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (N : Z.Modules) :
    ((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) f g).hom.app
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj N) ≫
      canonicalSinglePullbackMap (f ≫ g) N =
    (derivedPullback f).map (canonicalSinglePullbackMap g N) ≫
      canonicalSinglePullbackMap f ((pullback g).obj N) ≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map
          ((pullbackComp f g).hom.app N)
```

## New

```lean
theorem canonicalSinglePullbackComposition
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (N : Z.Modules) :
    ((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) f g).hom.app
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj N) ≫
      canonicalSinglePullbackMap (f ≫ g) N =
    (AlgebraicGeometry.derivedPullback f).map (canonicalSinglePullbackMap g N) ≫
      canonicalSinglePullbackMap f ((pullback g).obj N) ≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map
          ((pullbackComp f g).hom.app N)
```

## Users

The live item is absent while quarantined. A source search through both `lean/`
and `quarantine/` finds exactly the following three direct importers and users
of the theorem; all remain quarantined. Their arguments and conclusions still
refer to the same selected composition and canonical comparison maps. The
restoration changes none of their intended types, so it forces no consumer
adaptation. Their existing independent rework remains their own assignment.
All parent DAG attachments and dependencies are preserved.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComposition | V2 | Restored item; qualified functor name, proved private helpers, local elaboration annotations, and proof-import update. Same intended statement. |
| Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackSquare | unclaimed | Quarantined direct importer; uses the theorem at both square paths. Same selected comparisons and theorem type; no adaptation forced. |
| Sheaf.AlgebraicGeometry.PicardDerivedUnitNormalizationComposition | unclaimed | Quarantined direct importer; uses the theorem on the structure module. Same theorem type; no adaptation forced. |
| Sheaf.AlgebraicGeometry.TensorSinglePullbackComposition | unclaimed | Quarantined direct importer; uses the theorem in the two tensor-coefficient calculations. Same theorem type; no adaptation forced. |

The transitive users inherit the same statement; no exported definition or
instance changed. Only the assigned item module is edited.

## Status

landed 20261021T004845-L-1795756 2026-10-21 (merge of deliver/V2/Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComposition)
