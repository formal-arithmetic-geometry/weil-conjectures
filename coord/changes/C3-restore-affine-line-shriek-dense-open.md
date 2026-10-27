# AlgebraicGeometry.exists_dense_open_affineLine_shriek_constructible

## Reason

Restore the module assigned by coord/rework.tsv from its quarantine archive to
lean/Sheaf/AlgebraicGeometry/EtaleAffineLineShriekFiniteTypeDenseOpen.lean.
The archived proof fails against the current library because
Scheme.isConstructibleEtaleModuleSheaf_iff was renamed upstream. Replace its
nine proof uses with Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf
and import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
privately in place of the retired Sheaf module. The restored file compiles in 9.1 seconds.

## Old

No module currently exists at the Lean path. The quarantine archive preserves the
following signature, which is restored verbatim:

```lean
theorem exists_dense_open_affineLine_shriek_constructible
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (Y : Scheme.{u}) [IsAffine Y]
    [Algebra.FiniteType ℤ Γ(Y, ⊤)]
    (F : Sheaf (AffineSpace (ULift.{u} (Fin 1)) Y).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)) (hF : Scheme.IsConstructibleEtaleModuleSheaf F)
    (c : Compactification (AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y)) (q : ℤ) :
    ∃ U : Y.Opens, Dense (U : Set Y) ∧
      Scheme.IsConstructibleEtaleModuleSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj
          ((_root_.DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
          ((_root_.DerivedCategory.Plus.singleFunctor
            (Sheaf (AffineSpace (ULift.{u} (Fin 1)) Y).smallEtaleTopology
              (ModuleCat.{u + 1} Λ)) 0).obj F))))
```

## New

The signature and public imports above are unchanged from quarantine. Both existing
proofs are preserved, with only the private comparison import and renamed comparison
theorem uses updated. No definition, instance, target statement, or DAG attachment changes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekFiniteTypeDenseOpen | C3 | Assigned restoration; private import and proof API migration. |
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekSheafConstructible | quarantined; no claim file | Archived parent imports and applies the restored theorem with the identical signature; no adaptation needed. |

The downstream tool with --allow-missing found zero current Lean importers and zero
current declaration users. The quarantined parent was checked separately. Restoration
preserves the node lem-weil-pbc-affine-line-shriek-finite-type-dense-open, all its existing
dependencies, and the unit route. No module is withdrawn and no archive is changed.

## Status

landed 20261022T113843-L-314135 2026-10-22 (merge of deliver/C3/Sheaf.AlgebraicGeometry.EtaleAffineLineShriekFiniteTypeDenseOpen)
