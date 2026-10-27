# AlgebraicGeometry.isConstructibleEtaleModuleSheaf_affineLine_shriek

## Reason

Restore the item assigned in coord/rework.tsv from its quarantine archive. The
archived proof fails against the current library because the duplicate comparison
module was retired and Scheme.isConstructibleEtaleModuleSheaf_iff was replaced
by the canonical source theorem. This migration was documented for this archive
in coord/changes/D9-constructible-etale-module-comparison-retirement.md.

The sandbox compile of the unchanged archive reported unknown comparison constants.
Changing its private comparison import and all eight comparison applications to
WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison and
Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf repairs the errors.
The complete restored file compiles in 7.6 seconds, with zero sorry.

## Old

The Lean path is absent; the quarantine archive preserves this exact signature:

```lean
theorem isConstructibleEtaleModuleSheaf_affineLine_shriek
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (Y : Scheme.{u}) [IsAffine Y]
    (F : Sheaf (AffineSpace (ULift.{u} (Fin 1)) Y).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)) (hF : Scheme.IsConstructibleEtaleModuleSheaf F)
    (c : Compactification (AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y)) (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
          ((_root_.DerivedCategory.Plus.singleFunctor
            (Sheaf (AffineSpace (ULift.{u} (Fin 1)) Y).smallEtaleTopology
              (ModuleCat.{u + 1} Λ)) 0).obj F)))
```

## New

The same signature, all private helper signatures, the complete proof, all public
imports and all docstrings are preserved. Only the private comparison import and
the eight proof applications are migrated to the existing source API. No definition,
instance, hypothesis, conclusion, target meaning, or DAG dependency changes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekSheafConstructible | K7 | Assigned restoration and proof API repair. |
| Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility | quarantined; not adapted | Its archived application at line 229 uses the identical restored signature. |

The read-only downstream tool with --allow-missing and --uses found zero live
importers and zero live declaration users. A separate search of quarantine found
the parent listed above. Its proof application remains valid without adaptation.
The node lem-weil-pbc-etale-affine-line-shriek-sheaf-constructible retains its Lean
attachment, all statement and proof dependencies, and its unit route. The archive
is untouched; no module is withdrawn. No consumer requires a forced adaptation.

## Status

landed 20261023T041118-L-1258706 2026-10-23 (merge of deliver/K7/Sheaf.AlgebraicGeometry.EtaleAffineLineShriekSheafConstructible)
