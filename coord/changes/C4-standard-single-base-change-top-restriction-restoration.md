# AlgebraicGeometry.standardSingleBaseChange_topRestriction_comparison

## Reason

Restore the missing source from the quarantine archive named by the assigned
rework row. The rollback removed the module, while its Lean attachment and its
quarantined consumer still require it. This restores the complete proved
theorem, rather than replacing it with an empty module or a new obligation.
Source: Stacks Project, Tags 08HY and 0D5S.

## Old

The current source path is absent. The preserved quarantine archive has this
signature:

```lean
theorem standardSingleBaseChange_topRestriction_comparison
    {Y B A : Scheme.{u}} (p : Y ⟶ B) (M : Y.Modules) (g : A ⟶ B) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let j := (⊤ : Y.Opens).ι
    let N := M.restrict j
    ∃ (e : (schemeDerivedDirectImage p).obj
          ((DerivedCategory.singleFunctor _ 0).obj M) ≅
        (schemeDerivedDirectImage (j ≫ p)).obj
          ((DerivedCategory.singleFunctor _ 0).obj N))
      (t : (schemeDerivedDirectImage (pullback.snd (j ≫ p) g)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (Scheme.Modules.tensorPullbackObj (pullback.fst (j ≫ p) g) N)) ≅
        (schemeDerivedDirectImage (pullback.snd p g)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (Scheme.Modules.tensorPullbackObj (pullback.fst p g) M))),
      standardSingleBaseChangeMap p M g =
        (derivedPullback g).map e.hom ≫
          standardSingleBaseChangeMap (j ≫ p) N g ≫ t.hom
```

## New

The same signature above and the whole archived module are restored verbatim
at `lean/Sheaf/AlgebraicGeometry/StandardSingleBaseChangeTopRestriction.lean`.
The complete proof is also unchanged:

```lean
  dsimp
  let e := standardSingleBaseChange_topRestriction_sourceIso p M
  exact ⟨e, standardSingleBaseChange_topRestriction_compatibility p M g e rfl⟩
```

No statement, definition, attribute or public import changes. The canonical
source isomorphism is constructed in the existing auxiliary module; its
compatibility theorem supplies the target isomorphism and equation. No data is
chosen from an unproved existence statement.

## Users

`tools/downstream.py ... --uses standardSingleBaseChange_topRestriction_comparison
--allow-missing` reports zero current source importers because this module and
its consumer are quarantined. A scan of both Lean roots and both quarantined
roots finds one direct importer and actual theorem user, listed below. Its
unchanged archived source compiled in 7.7 seconds against the restored theorem.
No consumer adaptation is required. Claim status is the shared snapshot at
inspection; the assigned item belongs to C4.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StandardSingleBaseChangeTopRestriction | C4 | Restore the missing module and complete proof verbatim. |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationPresentationData | unclaimed | Archived direct consumer; original statement and proof compile unchanged. |

The DAG attachment `lem-pc-standard-single-base-change-top-restriction` and all
its dependency records are preserved. The parent
`lem-pc-standard-single-flat-counit-localization-presentation-data` continues to
use this theorem in its fourth step. The unit `sk-thm-picard-coherence` is
unchanged. No target meaning changes or target statement review is reopened.

## Status

landed 20261021T013340-L-2288273 2026-10-21 (merge of deliver/C4/Sheaf.AlgebraicGeometry.StandardSingleBaseChangeTopRestriction)
