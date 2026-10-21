# AlgebraicGeometry.standardSingleBaseChangeMap

## Reason

Restore the concrete canonical comparison quarantined by the 2026-10-20 cluster
restore. The current rework row records the missing source path and its archive;
the stage-3 queue reports 113 quarantined importers waiting on this root. The
repair reinstates the actual definition, while preserving the archive, the
existing Lean attachment, and all statement and proof dependencies. No target
statement, source-library declaration, or existing definition is changed.

## Old

The current Lean source file is absent. The preserved archive contains this
verbatim definition:

```lean
noncomputable def standardSingleBaseChangeMap
    {Y B A : Scheme.{u}} (p : Y ⟶ B) (M : Y.Modules) (g : A ⟶ B) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (derivedPullback g).obj ((schemeDerivedDirectImage p).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M)) ⟶
    (schemeDerivedDirectImage (pullback.snd p g)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings (pullback p g).toRingedSpace)) 0).obj
          (Scheme.Modules.tensorPullbackObj (pullback.fst p g) M)) :=
  letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  schemeDerivedBaseChangeMap p (pullback.snd p g) g (pullback.fst p g)
    pullback.condition ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M) ≫
    (schemeDerivedDirectImage (pullback.snd p g)).map
      (Scheme.picardTermwiseSingleMap (pullback.fst p g) M)
```

## New

The original Lean source path again contains the same definition verbatim:

```lean
noncomputable def standardSingleBaseChangeMap
    {Y B A : Scheme.{u}} (p : Y ⟶ B) (M : Y.Modules) (g : A ⟶ B) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (derivedPullback g).obj ((schemeDerivedDirectImage p).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M)) ⟶
    (schemeDerivedDirectImage (pullback.snd p g)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings (pullback p g).toRingedSpace)) 0).obj
          (Scheme.Modules.tensorPullbackObj (pullback.fst p g) M)) :=
  letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  schemeDerivedBaseChangeMap p (pullback.snd p g) g (pullback.fst p g)
    pullback.condition ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M) ≫
    (schemeDerivedDirectImage (pullback.snd p g)).map
      (Scheme.picardTermwiseSingleMap (pullback.fst p g) M)
```

The three public imports, public section, module header, options and docstrings
are also restored verbatim. This is source restoration rather than a change of
mathematical construction. The first factor is the existing canonical derived
mate and the second is direct image of the existing pinned single pullback map.
No `sorry`, arbitrary existence witness, flatness assumption or isomorphism
assertion is added. The source is Stacks Tags 08HY, 0A1D and 0DJ9.

## Users

`tools/downstream.py ... --uses standardSingleBaseChangeMap --allow-missing`
reports no current importers because the root and its consumers are
quarantined. An additional source scan of both Lean roots and the quarantine
finds the users below, including all eleven archived direct importers. Their
statements retain exactly the same meaning: the declaration's signature,
constructed map and public imports are restored unchanged. No consumer edit is
required or delivered. The remaining transitive consumers also receive the
original interface. Holder values reflect the shared claim records at inspection.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.StandardSingleBaseChangeMap | E1 | Restores the missing real definition. |
| Sheaf.AlgebraicGeometry.StandardFlatSingleBaseChange | unclaimed | Archived consumer; exact original type, body and public imports restored; no adaptation. |
| Sheaf.AlgebraicGeometry.StandardFlatSingleBaseChangeEpi | unclaimed | Archived consumer; exact original type, body and public imports restored; no adaptation. |
| Sheaf.AlgebraicGeometry.StandardFlatSingleBaseChangeMono | unclaimed | Archived consumer; exact original type, body and public imports restored; no adaptation. |
| Sheaf.AlgebraicGeometry.StandardSingleBaseChangeTopRestriction | unclaimed | Archived consumer; exact original type, body and public imports restored; no adaptation. |
| Sheaf.AlgebraicGeometry.StandardSingleBaseChangeTopRestrictionAux | unclaimed | Archived consumer; exact original type, body and public imports restored; no adaptation. |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitAffine | unclaimed | Archived consumer; exact original type, body and public imports restored; no adaptation. |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalization | unclaimed | Archived consumer; exact original type, body and public imports restored; no adaptation. |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationCompletion | unclaimed | Archived consumer; exact original type, body and public imports restored; no adaptation. |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationHomology | unclaimed | Archived consumer; exact original type, body and public imports restored; no adaptation. |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitPresentation | unclaimed | Archived consumer; exact original type, body and public imports restored; no adaptation. |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitUnionEquation | unclaimed | Archived consumer; exact original type, body and public imports restored; no adaptation. |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitUnionTriangles | unclaimed | Archived consumer; exact original type, body and public imports restored; no adaptation. |
| Sheaf.AlgebraicGeometry.StandardSingleOpenRelativeArrow | unclaimed | Archived consumer; exact original type, body and public imports restored; no adaptation. |
| Sheaf.AlgebraicGeometry.StandardSingleOpenStalkArrow | unclaimed | Archived consumer; exact original type, body and public imports restored; no adaptation. |
| Sheaf.AlgebraicGeometry.StandardSingleStalkFlatCounitModel | unclaimed | Archived consumer; exact original type, body and public imports restored; no adaptation. |
| Sheaf.AlgebraicGeometry.StandardSingleUnionHomotopyChainData | unclaimed | Archived consumer; exact original type, body and public imports restored; no adaptation. |
| Sheaf.AlgebraicGeometry.StandardSingleUnionSESChainData | unclaimed | Archived consumer; exact original type, body and public imports restored; no adaptation. |
| Sheaf.AlgebraicGeometry.StandardSingleUnionSESPresentation | unclaimed | Archived consumer; exact original type, body and public imports restored; no adaptation. |

The DAG node `def-pc-standard-single-base-change-map` is retained unchanged, as
are its parent references. The unit `sk-thm-picard-coherence` and its realized
route remain unchanged. Restoration introduces no new target meaning; target
statement review is not reopened by a changed definition.

## Status

landed 20261021T002133-L-1490827 2026-10-21 (merge of deliver/E1/Sheaf.AlgebraicGeometry.StandardSingleBaseChangeMap)
