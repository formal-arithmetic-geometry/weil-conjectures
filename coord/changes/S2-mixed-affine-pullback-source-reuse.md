# AlgebraicGeometry.exists_mixedAffineSections_pullback_unit_normalization

## Reason

Restore the quarantined Sheaf module without duplicating the adopted source theorem.
The archive imports the withdrawn Sheaf IsKFlatTilde module; an initial compile reports
`Unknown identifier isKFlat_tilde`. The adopted source already contains the full proof
using its IsKFlatTensor API. Its public theorem signature is byte-for-byte identical
to the archived signature. Reuse that proof through a compatibility import and correct
the node's Lean attachment. This is a source-reuse repair, not a theorem withdrawal.
The archive itself and every mathematical dependency are preserved.

## Old

The archived module declares the following public theorem, with a complete proof:

```lean
theorem exists_mixedAffineSections_pullback_unit_normalization
    {S T : Scheme.{u}} [IsAffine S] [IsAffine T] (g : T ⟶ S) :
    let F : ModuleCat.{u} Γ(S, ⊤) ⥤
        SheafOfModules.{u} (moduleRings S.toRingedSpace) :=
      tilde.functor Γ(S, ⊤) ⋙ Scheme.Modules.restrictFunctor S.toSpecΓ
    let H := RingedSpace.globalSectionsFunctor S.toRingedSpace
    let J := RingedSpace.globalSectionsFunctor T.toRingedSpace
    let K : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings T.toRingedSpace) := Scheme.Modules.tensorPullback g
    let R := ModuleCat.restrictScalars.{u} g.appTop.hom
    let d : F ⋙ H ⟶ F ⋙ K ⋙ J ⋙ R :=
      Functor.whiskerRight (Functor.whiskerLeft F
        (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit) H
    ∀ [F.Additive] [H.Additive] [J.Additive] [K.Additive]
      (P : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℤ)
      (_hP : (HomologicalComplex.quasiIso (ModuleCat.{u} Γ(S, ⊤)) (.up ℤ)).kFlat P),
    let C := (F.mapHomologicalComplex (.up ℤ)).obj P
    let Q : DerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) := DerivedCategory.Q.obj C
    let Y := ((F ⋙ K ⋙ J).mapHomologicalComplex (.up ℤ)).obj P
    ∃ b : (schemeDerivedGlobalSections T).obj ((derivedPullback g).obj Q) ≅
        DerivedCategory.Q.obj Y,
      mixedSectionsComplexUnit S C ≫
        (schemeDerivedGlobalSections S).map ((schemeHomPullbackAdjunction g).unit.app Q) ≫
          (mixedGlobalSectionsDirectImageIso g).hom.app ((derivedPullback g).obj Q) ≫
            (schemeGlobalScalarRestriction g).map b.hom =
      DerivedCategory.Q.map ((d.mapHomologicalComplex (.up ℤ)).app P) ≫
        R.mapDerivedCategoryFactors.inv.app Y
```

It publicly imports MixedAffineSectionsComplexUnit and the Sheaf compatibility path
MixedGlobalSectionsDirectImageIso. Its proof privately imports the retired Sheaf
IsKFlatTilde and the other K-flat/chart/counit dependencies.

## New

The restored Sheaf module retains both original public imports and adds:

```lean
public import WeilConjectures.AlgebraicGeometry.MixedAffineSectionsPullbackUnitNormalization
```

The fully qualified theorem above is re-exported from this adopted source module.
There is one declaration with precisely the same signature, universes and visibility.
The source implementation supplies the original K-flat/chart/counit proof, and its
existing signatures, attributes, public imports and proof bodies are untouched.
The DAG node keeps its statement, proof, proof_deps, stmt_deps and unit; only its
Lean attachment now names the source file containing that declaration.
No definition changes and no target meaning review is reopened.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.MixedAffineSectionsPullbackUnitNormalization | S2 | Restore as a compatibility import; same theorem and original public imports. |
| WeilConjectures.AlgebraicGeometry.MixedAffineSectionsChartModelFactorization | unclaimed in shared snapshot | The existing source consumer already imports the source theorem; unchanged. |
| WeilConjectures | unclaimed in shared snapshot | Existing source aggregate imports the same source theorem; unchanged. |

`tools/downstream.py` with `--allow-missing --uses` finds zero current downstream
modules of the absent Sheaf path. This does not justify withdrawal: the parent node
lem-sc-mixed-affine-sections-chart-model-factorization still uses this node, and its
live source consumer applies exactly this theorem. The parent dependency is preserved.
The two rows above are all direct source-module importers. No consumer is adapted.
Quarantined paths and source-library declarations are neither deleted nor edited.

## Status

landed 20261021T225210-L-3794310 2026-10-21 (merge of deliver/S2/Sheaf.AlgebraicGeometry.MixedAffineSectionsPullbackUnitNormalization)
