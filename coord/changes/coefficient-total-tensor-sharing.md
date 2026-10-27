# coefficientTotalTensor

## Reason

Withdrawn by the independent reviewers (cc, 2026-10-22, heads ee26d713db5, 4ada08f3dec5 and
91a912d96cae; the first withdrawal was lost at landing because its fix file was misnamed, the second
because its Status line was not `open`, which the delivery checker requires of every delivered record). The delivery rewrote the body of
`coefficientTotalTensor` in the unclaimed module `Sheaf.Paper.CoefficientRingedTensorHomModel`
(47 direct importers) to call a new `coefficientTotalTensorGeneral`. That change was not
forced and broke an importer: `Sheaf.Paper.IntegralTensorReductionTowerComparison`
(line 122, `simp only [coefficientTotalTensor, Functor.uncurry_obj_map,
Functor.map₂HomologicalComplex, …]` followed by `rw [ScalarHomTensor.tensorMap_factor]`
no longer finds its pattern, because the unfolded term is now `coefficientTotalTensorGeneral …`).
`Sheaf.Paper.IntegralTensorTransitionCompatibility` and
`Sheaf.Paper.InternalSectionTotalComparison` exceeded 60 s against it, while all three compile
against the published module (36–44 s). Rechecked on head 4ada08f3dec5: the same importer
fails at 122:12 against the delivered module. Head 91a912d96cae re-delivers the same module byte for
byte, so the withdrawal stands.

`Sheaf.Paper.CoefficientRingedTensorHomModel` is therefore kept byte for byte at its published
text. `WeilConjectures.coefficientTotalTensorGeneral`, with the same signature and body
`Functor.uncurry.obj ((curriedTensor D).map₂CochainComplex)`, is defined in the new Y7 module
`Sheaf.Paper.FiniteCoefficientSiteTensorNaturality` (node
lem-sf-finite-coefficient-site-tensor-naturality). Its only use is that module, where
`target_total_eq` identifies it with `coefficientTotalTensor` at the pro-étale constant ring by
`rfl` (`map₂CochainComplex` is an abbreviation of `map₂HomologicalComplex _ _ _`).

## Old

```lean
noncomputable def coefficientTotalTensor
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
    (A : Sheaf J CommRingCat.{max c v u}) :
    CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ ×
    CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ ⥤
    CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ :=
  letI := (SheafOfModules.isMonoidal_W_independentCoefficients A)
  letI := SheafOfModules.monoidalCategory A
  letI := (SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients A)
  letI := (SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients A)
  Functor.uncurry.obj
    (Functor.map₂HomologicalComplex (MonoidalCategory.curriedTensor (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)))
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
```

## New

Unchanged: `coefficientTotalTensor` and its module keep the text above. Added, in the new module
`Sheaf.Paper.FiniteCoefficientSiteTensorNaturality`:

```lean
noncomputable def coefficientTotalTensorGeneral
    (D : Type a) [Category.{b} D] [Preadditive D] [MonoidalCategory D]
    [(curriedTensor D).PreservesZeroMorphisms]
    [∀ M, ((curriedTensor D).obj M).PreservesZeroMorphisms]
    [∀ P Q : CochainComplex D ℤ,
      HomologicalComplex.HasMapBifunctor P Q (curriedTensor D) (.up ℤ)] :
    CochainComplex D ℤ × CochainComplex D ℤ ⥤ CochainComplex D ℤ :=
  Functor.uncurry.obj ((curriedTensor D).map₂CochainComplex)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientRingedTensorHomModel | unclaimed | Unchanged (published text). |
| Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison | unclaimed | Unchanged; uses the published `coefficientTotalTensor`. |
| Sheaf.Paper.FiniteCoefficientSiteTensorNaturality | new, Y7 | Defines and uses `coefficientTotalTensorGeneral`. |

No other module uses `coefficientTotalTensorGeneral`.

## Status

landed 20261022T114256-L-598666 2026-10-22 (merge of deliver/Y7/Sheaf.Paper.FiniteCoefficientSiteHomArrow)
