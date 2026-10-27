# scalarTensorSection

## Reason

Extract the existing pure-tensor definition to its own API module. This removes the import cycle when completion coherence reuses the already proved ordinary scalar associator and unit from RingedKFlatWordComparisonDescent. The original module publicly reexports the definition. No definition body or mathematical signature changes.

## Old

```lean
noncomputable def scalarTensorSection
    (F : SheafOfModules.DerivedChangeOfRingsCochainModel a)
    (M : ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R))
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) : (F.E.obj M).val.obj U :=
  (eqToHom (F.obj_eq M).symm).val.app U
    ((toSheafify J (SheafOfModules.changeOfRingsPresheaf a M).presheaf).app U
      (s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x))
```

## New

The same declaration, verbatim, in `Sheaf.Algebra.Homology.ScalarTensorSection`:

```lean
noncomputable def scalarTensorSection
    (F : SheafOfModules.DerivedChangeOfRingsCochainModel a)
    (M : ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R))
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) : (F.E.obj M).val.obj U :=
  (eqToHom (F.obj_eq M).symm).val.app U
    ((toSheafify J (SheafOfModules.changeOfRingsPresheaf a M).presheaf).app U
      (s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.FiniteFreeCompletionExchangeCoherence | B4 | Publicly imports and reexports the extracted definition; reuses the scalar associator and unit. |
| Sheaf.Algebra.Homology.RingedKFlatWordComparisonDescent | unclaimed | Changes its public import to ScalarTensorSection; keeps the section constructor locally irreducible and controls unfolding in two private proofs; public signatures unchanged. |
| Sheaf.Algebra.Homology.SectionsScalarDerivedTransport | unclaimed | No change: the coherence module still publicly reexports the identical definition. |

The scalar-descent adaptation compiled cleanly in 37.2 seconds. The scalar-descent file also uses `attribute [local irreducible] scalarTensorSection`, unfolds it once in `scalar_section_smul`, and makes it locally semireducible for `scalar_adjunction` only. Profiling identified repeated reduction of the sheafified tensor expression. These local proof edits bound that reduction and alter no declaration signature.

All further downstream users keep the same definition and public statements. No target semantics change; this is an API extraction.

## Status

landed 20261025T201357-L-2465468 2026-10-25 (merge of deliver/B4/Sheaf.Algebra.Homology.FiniteFreeCompletionExchangeCoherence)
