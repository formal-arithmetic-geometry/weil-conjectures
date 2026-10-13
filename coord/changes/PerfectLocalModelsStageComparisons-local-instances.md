# AlgebraicGeometry.perfect_local_models_stage_comparisons

## Reason

The stage-3 static interface scanner flags any new attribute command, including
this local command. This record documents the inference change, not a changed
mathematical statement. The named transparent abelian structures abbreviate the
existing canonical Mathlib structures and avoid repeatedly expanding them while
elaborating derived restriction categories. No definition, universe, binder or
conclusion changes. The local attribute ends with this namespace/file and is not
exported to importers. No target semantic review is reopened.

## Old

The original declaration signature, verbatim:

```lean
theorem perfect_local_models_stage_comparisons
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    :
    let Yj := pullback t (Spec.map (R.map (homOfLE hij)))
    let X := pullback t (Spec.map (c.ι.app i))
    let gj := baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))
    ∀ (U V : Yj.Opens) (hcover : U ⊔ V = ⊤)
      (hU : IsCompact (U : Set Yj)) (hV : IsCompact (V : Set Yj))
      (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
      (hA : U.toScheme.IsPerfect A) (hB : V.toScheme.IsPerfect B)
      (E : schemeDerivedCategory X)
      (φU : (derivedPullback (gj ∣_ U)).obj A ≅
        (schemeOpenRestriction X (gj ⁻¹ᵁ U)).mapDerivedCategory.obj E)
      (φV : (derivedPullback (gj ∣_ V)).obj B ≅
        (schemeOpenRestriction X (gj ⁻¹ᵁ V)).mapDerivedCategory.obj E),
    ∃ (k : I) (hjk : j ≤ k),
      let g := baseChangeMap t
        (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (T' := Over.mk (Spec.map (c.ι.app i)))
        (Over.homMk (Spec.map (c.ι.app k))
          (by dsimp; rw [← Spec.map_comp, c.w (homOfLE (hij.trans hjk))]))
      ∃ (F : schemeDerivedCategory
          (pullback t (Spec.map (R.map (homOfLE (hij.trans hjk)))))),
        ∃ (U' V' : (pullback t
            (Spec.map (R.map (homOfLE (hij.trans hjk))))).Opens),
          U' ⊔ V' = ⊤ ∧
          U'.toScheme.IsPerfect ((derivedPullback U'.ι).obj F) ∧
          V'.toScheme.IsPerfect ((derivedPullback V'.ι).obj F) ∧
        let P := gj ⁻¹ᵁ U
        let Q := gj ⁻¹ᵁ V
        let L := (derivedPullback g).obj F
        let RU := (SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) P).mapDerivedCategory
        let RV := (SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) Q).mapDerivedCategory
        ∃ (pU : RU.obj L ≅ RU.obj E) (pV : RV.obj L ≅ RV.obj E),
          derivedOpenHomRestriction X.toRingedSpace
              (homOfLE (show P ⊓ Q ≤ P from inf_le_left)) (E := L) (F := E) pU.hom =
            derivedOpenHomRestriction X.toRingedSpace
              (homOfLE (show P ⊓ Q ≤ Q from inf_le_right)) (E := L) (F := E) pV.hom
```

There was no local instance-selection command after `namespace AlgebraicGeometry`.

## New

The declaration signature remains verbatim:

```lean
theorem perfect_local_models_stage_comparisons
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    :
    let Yj := pullback t (Spec.map (R.map (homOfLE hij)))
    let X := pullback t (Spec.map (c.ι.app i))
    let gj := baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))
    ∀ (U V : Yj.Opens) (hcover : U ⊔ V = ⊤)
      (hU : IsCompact (U : Set Yj)) (hV : IsCompact (V : Set Yj))
      (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
      (hA : U.toScheme.IsPerfect A) (hB : V.toScheme.IsPerfect B)
      (E : schemeDerivedCategory X)
      (φU : (derivedPullback (gj ∣_ U)).obj A ≅
        (schemeOpenRestriction X (gj ⁻¹ᵁ U)).mapDerivedCategory.obj E)
      (φV : (derivedPullback (gj ∣_ V)).obj B ≅
        (schemeOpenRestriction X (gj ⁻¹ᵁ V)).mapDerivedCategory.obj E),
    ∃ (k : I) (hjk : j ≤ k),
      let g := baseChangeMap t
        (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (T' := Over.mk (Spec.map (c.ι.app i)))
        (Over.homMk (Spec.map (c.ι.app k))
          (by dsimp; rw [← Spec.map_comp, c.w (homOfLE (hij.trans hjk))]))
      ∃ (F : schemeDerivedCategory
          (pullback t (Spec.map (R.map (homOfLE (hij.trans hjk)))))),
        ∃ (U' V' : (pullback t
            (Spec.map (R.map (homOfLE (hij.trans hjk))))).Opens),
          U' ⊔ V' = ⊤ ∧
          U'.toScheme.IsPerfect ((derivedPullback U'.ι).obj F) ∧
          V'.toScheme.IsPerfect ((derivedPullback V'.ι).obj F) ∧
        let P := gj ⁻¹ᵁ U
        let Q := gj ⁻¹ᵁ V
        let L := (derivedPullback g).obj F
        let RU := (SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) P).mapDerivedCategory
        let RV := (SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) Q).mapDerivedCategory
        ∃ (pU : RU.obj L ≅ RU.obj E) (pV : RV.obj L ≅ RV.obj E),
          derivedOpenHomRestriction X.toRingedSpace
              (homOfLE (show P ⊓ Q ≤ P from inf_le_left)) (E := L) (F := E) pU.hom =
            derivedOpenHomRestriction X.toRingedSpace
              (homOfLE (show P ⊓ Q ≤ Q from inf_le_right)) (E := L) (F := E) pV.hom
```

The new command after `namespace AlgebraicGeometry` is exactly:

```lean
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
```

The named abbreviations come from the privately imported transition module's
public dependency `Sheaf.AlgebraicGeometry.OpenSectionsCohomologyModel`. They
abbreviate existing Mathlib structures; they add no axioms or unknown data.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsStageComparisons | F1 | Local inference only; same public signature. |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsStageGluing | unclaimed | Direct user of the unchanged theorem; no adaptation. |

`tools/downstream.py Sheaf.AlgebraicGeometry.PerfectLocalModelsStageComparisons
--uses openComparisonModuleAbelian openComparisonOverModuleAbelian` found 417
transitive importers and zero mentions of either abbreviation in them. No
existing downstream module is adapted. The command is local, so all importers
retain their instance-selection environment and their existing statements.
The new transition module has its own local instance commands and no baseline
importers. Its signature is documented by its new node.

## Status

landed 20261013T190139-L-3215863 2026-10-13 (merge of deliver/F1/Sheaf.AlgebraicGeometry.PerfectLocalModelsStageComparisons)
