# AlgebraicGeometry.higherDirectImage_coefficient_comparison

## Reason

The human-approved retirement queue, `coord/retire-items.tsv`, assigns the Sheaf
copy for retirement in favor of its adopted source-library twin. The old scan
classified the pair as DIFFERENT. On the current source the sole signature
text difference is an explicit `SheafOfModules.{u}` universe annotation in the
twin. Applying the twin theorem to the complete original type compiles, and
`#print axioms` for that check and the source theorem lists only `propext`,
`Classical.choice` and `Quot.sound`.

Both declarations give the same coefficient-natural transformation and the same
formula for every injective resolution. Empty opens and degree zero are included
in the type without extra hypotheses. Their proof route and dependencies agree.
Retire the duplicate file and move its DAG Lean attachment to the source theorem.

## Old

Module: `Sheaf.AlgebraicGeometry.HigherDirectImageCoefficientComparison`.

```lean
theorem higherDirectImage_coefficient_comparison
    {X Y : Scheme.{u}} (f : X ⟶ Y) (p : ℕ) :
    ∃ c : ∀ V : Y.Opens,
      Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι ⋙
        RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p ⋙
          forget₂ (ModuleCat.{u}
            ((moduleRings (f ⁻¹ᵁ V).toScheme.toRingedSpace).obj.obj (Opposite.op ⊤)))
              AddCommGrpCat.{u} ⟶
      (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p ⋙
        RingedSpace.openModuleSections Y.toRingedSpace V,
      ∀ (N : X.Modules) (I : InjectiveResolution
        (show SheafOfModules (moduleRings X.toRingedSpace) from N)) (V : Y.Opens),
        let K := ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex
        ∃ e :
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι ⋙
            RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p ⋙
              forget₂ (ModuleCat.{u}
                ((moduleRings (f ⁻¹ᵁ V).toScheme.toRingedSpace).obj.obj (Opposite.op ⊤)))
                  AddCommGrpCat.{u}).obj N) ≅
            (Scheme.Modules.sectionCohomologyPresheaf K p).presheaf.obj (Opposite.op V),
          (c V).app N = e.hom ≫
            ((PresheafOfModules.toPresheaf (moduleRings Y.toRingedSpace).obj).map
              (Scheme.Modules.sectionCohomologyTheta K p ≫
                (SheafOfModules.forget (moduleRings Y.toRingedSpace)).map
                  (I.isoRightDerivedObj
                    (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) p).inv)).app
                      (Opposite.op V)
```

## New

Existing module: `WeilConjectures.AlgebraicGeometry.HigherDirectImageCoefficientComparison`.

```lean
theorem higherDirectImage_coefficient_comparison
    {X Y : Scheme.{u}} (f : X ⟶ Y) (p : ℕ) :
    ∃ c : ∀ V : Y.Opens,
      Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι ⋙
        RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p ⋙
          forget₂ (ModuleCat.{u}
            ((moduleRings (f ⁻¹ᵁ V).toScheme.toRingedSpace).obj.obj (Opposite.op ⊤)))
              AddCommGrpCat.{u} ⟶
      (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p ⋙
        RingedSpace.openModuleSections Y.toRingedSpace V,
      ∀ (N : X.Modules) (I : InjectiveResolution
        (show SheafOfModules.{u} (moduleRings X.toRingedSpace) from N)) (V : Y.Opens),
        let K := ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex
        ∃ e :
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι ⋙
            RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p ⋙
              forget₂ (ModuleCat.{u}
                ((moduleRings (f ⁻¹ᵁ V).toScheme.toRingedSpace).obj.obj (Opposite.op ⊤)))
                  AddCommGrpCat.{u}).obj N) ≅
            (Scheme.Modules.sectionCohomologyPresheaf K p).presheaf.obj (Opposite.op V),
          (c V).app N = e.hom ≫
            ((PresheafOfModules.toPresheaf (moduleRings Y.toRingedSpace).obj).map
              (Scheme.Modules.sectionCohomologyTheta K p ≫
                (SheafOfModules.forget (moduleRings Y.toRingedSpace)).map
                  (I.isoRightDerivedObj
                    (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) p).inv)).app
                      (Opposite.op V)
```

The source file is preserved verbatim. The Sheaf path is withdrawn through
`deleted.txt`; the DAG node now records the existing source declaration.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.HigherDirectImageCoefficientComparison | M9 | Retired duplicate; no holes removed or added. |
| WeilConjectures.AlgebraicGeometry.HigherDirectImageCoefficientComparison | unclaimed; not adapted | Existing theorem supplies the identical elaborated statement. |
| WeilConjectures.AlgebraicGeometry.HigherDirectImageAffineCohomologyPresentation | unclaimed; not adapted | Sole DAG parent already imports the source twin and calls the theorem; original file compiles unchanged. |

`tools/downstream.py` reports zero downstream modules and only the retired file
as a textual use within that downstream set. A complete import scan of `lean/`
and `quarantine/` finds no importers of the retired module. The queue's old
consumer `Sheaf.AlgebraicGeometry.HigherDirectImageAffineCohomologyPresentation`
has already been retired; its node points to the source module in the table.
The sole DAG parent retains its dependency on this node, whose attachment now
selects the source theorem. The unit record realizes neither node directly;
no unit statement or proof step changes. All eight prerequisite Sheaf copies
listed in the retirement row are already absent.

## Status

landed 20261020T221257-L-4168206 2026-10-20 (merge of deliver/M9/Sheaf.AlgebraicGeometry.HigherDirectImageCoefficientComparison)
