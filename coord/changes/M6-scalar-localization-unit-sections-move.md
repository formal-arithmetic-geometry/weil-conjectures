# CategoryTheory.scalarLocalizationTelescopeUnitSections

## Reason

The ordinary module-colimit and complex-colimit helpers need the same normalization
predicate as the item theorem. Keeping its declaration in the item would create an
import cycle. Move its unchanged signature and body to the new tensor-comparison
helper, publicly imported by the original module. No mathematical definition changes.

## Old

In Sheaf.CategoryTheory.ScalarLocalizationUnderlyingTelescope:

```lean
def scalarLocalizationTelescopeUnitSections
    {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S)
    (M : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (N : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (e : N = SheafOfModules.changeOfRings φ M)
    (η : M ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj N) : Prop :=
  ∀ (V : Cᵒᵖ) (x : M.val.obj V),
    (η ≫ (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).map (eqToHom e)).val.app V x =
      (toSheafify J (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app V
        ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] x)
```

## New

The identical declaration above is in
Sheaf.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison. The original module
publicly imports it. All existing importers retain the same public name and body.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.ScalarLocalizationUnderlyingTelescope | M6 | Publicly imports the unchanged declaration instead of defining it locally. |
| Sheaf.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison | new, M6 | Owns the unchanged declaration. |
| Sheaf.CategoryTheory.ScalarLocalizationModuleColimit | new, M6 | Uses the common normalization predicate. |
| Sheaf.CategoryTheory.ScalarLocalizationTelescopeCore | new, M6 | Uses the common normalization predicate. |

The downstream query reports one existing module using the name: the item itself.
There are no other existing consumers to adapt. Target statements and the meaning of
all existing definitions remain unchanged.

## Status

landed 20261020T122112-L-477212 2026-10-20 (merge of deliver/M6/Sheaf.CategoryTheory.ScalarLocalizationUnderlyingTelescope)
