# AlgebraicGeometry.Scheme.affine_principal_cover_quasiIso_detection

## Reason

Retire the duplicate Sheaf module under the human-approved retirement of
2026-10-20 and its row in coord/retire-items.tsv. The official twin already
proves exactly the same public theorem. No Lean source currently imports the
Sheaf copy. The row's former consumer, Sheaf.AlgebraicGeometry.AffineOpenLocalizedModel,
has already been removed, and its official twin already imports the official
quasi-isomorphism detection module.

## Old

Module: Sheaf.AlgebraicGeometry.AffinePrincipalCoverQuasiIsoDetection.
The node lem-sc-affine-principal-cover-quasi-iso-detection points to its theorem:

```lean
theorem affine_principal_cover_quasiIso_detection
    (X : Scheme.{u}) [IsAffine X] (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (T : ModuleCat.{u} (X.presheaf.obj (.op ⊤)) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace)) [T.PreservesZeroMorphisms]
    (hT : Nonempty (T ≅ tilde.functor (X.presheaf.obj (.op ⊤)) ⋙
      Modules.restrictFunctor X.isoSpec.hom))
    (r : ℕ) (f : Fin r → X.presheaf.obj (.op ⊤))
    (hsub : ∀ j, X.basicOpen (f j) ≤ U)
    (hcover : ∀ x : X, x ∈ U → ∃ j, x ∈ X.basicOpen (f j))
    (F M : CochainComplex (ModuleCat.{u} (X.presheaf.obj (.op ⊤))) ℤ) (α : F ⟶ M)
    (hα : ∀ j : Fin r, QuasiIso ((Functor.mapHomologicalComplex
      (ModuleCat.extendScalars
        (algebraMap (X.presheaf.obj (.op ⊤)) (Localization.Away (f j))))
      (ComplexShape.up ℤ)).map α)) :
    IsIso (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Modules.overEquiv U)).mapDerivedCategory.map
      (DerivedCategory.Q.map ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map α)))
```

## New

Withdraw the duplicate module through deleted.txt. The delivery tool writes
an empty module pending the maintainer's physical pruning. Point the existing
DAG node to WeilConjectures.AlgebraicGeometry.AffinePrincipalCoverQuasiIsoDetection,
whose public theorem has the verbatim signature above. The upstream file is
unchanged. Its private helpers explicitly fix the overFunctor universe where
the duplicate inferred it; this does not change any public signature.
The node's mathematical statement, proof, proof dependencies, and unit stay unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineOpenLocalizedModel | absent from current tree | Former consumer already retired; no adaptation |
| WeilConjectures.AlgebraicGeometry.AffineOpenLocalizedModel | unchanged upstream | Already imports and applies the official theorem; compile checked |
| WeilConjectures | unchanged upstream | Already publicly imports the official twin |

A complete rg scan of lean/Sheaf and lean/WeilConjectures found no imports or
qualified references to the retired Sheaf module outside the module itself.
The only matching DAG attachment is updated in this delivery. There are no
forced adaptations and no changed definitions or target statements.

## Status

landed 20261020T132050-L-1408569 2026-10-20 (merge of deliver/V2/Sheaf.AlgebraicGeometry.AffinePrincipalCoverQuasiIsoDetection)
