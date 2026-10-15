# CategoryTheory.Mod.extendForgetTensorObjIso and extendForgetTensorIso

## Reason

Repair H4 of reviewer X-84c36. The item duplicated these existing definitions as
`extendTensorIso` and `forgetExtendIsoTensor`. Remove both complete duplicates and expose
these two existing definitions for reuse. The reviewer explicitly requests these visibility
changes. The dependency module is unclaimed in the local claims snapshot. The types,
construction bodies, instance hypotheses and public imports stay unchanged. No target changes
meaning, and no consumer needs an adaptation.

## Old

Within the existing `CategoryTheory.Mod` variable context:

```lean
private noncomputable def extendForgetTensorObjIso (M : Mod C R) :
    (extendScalarsObj φ M).X ≅ (((comap φ).obj (regular S)) ⊗ M).X where
  hom := extendDescHom φ (tensorObjπ ((comap φ).obj (regular S)) M) (by
    rw [← restrictedRegular_rightAction φ]
    exact tensorObjπ_condition ((comap φ).obj (regular S)) M)
  inv := coequalizer.desc (extendπ φ M) (by
    change ((β_ S R).hom ≫ γ[R,((comap φ).obj (regular S)).X]) ▷ M.X ≫
        extendπ φ M = _
    rw [restrictedRegular_rightAction φ]
    exact extendπ_condition φ M)
  hom_inv_id := by
    apply coequalizer.hom_ext
    simp only [extendDescHom, extendπ, tensorObjπ, coequalizer.π_desc_assoc]
    erw [coequalizer.π_desc, Category.comp_id]
    rfl
  inv_hom_id := by
    apply coequalizer.hom_ext
    simp only [extendDescHom, extendπ, tensorObjπ, coequalizer.π_desc_assoc]
    erw [coequalizer.π_desc, Category.comp_id]
    rfl

private noncomputable def extendForgetTensorIso :
    extendScalars φ ⋙ forget S ≅
      tensorLeft ((comap φ).obj (regular S)) ⋙ forget R :=
  NatIso.ofComponents (extendForgetTensorObjIso φ) (by
    intro M N f
    apply (cancel_epi (extendπ φ M)).1
    simp [extendForgetTensorObjIso, extendπ_extendScalarsMap_assoc,
      tensorObjπ_whiskerLeft]
    rfl)
```

## New

```lean
noncomputable def extendForgetTensorObjIso (M : Mod C R) :
    (extendScalarsObj φ M).X ≅ (((comap φ).obj (regular S)) ⊗ M).X where
  hom := extendDescHom φ (tensorObjπ ((comap φ).obj (regular S)) M) (by
    rw [← restrictedRegular_rightAction φ]
    exact tensorObjπ_condition ((comap φ).obj (regular S)) M)
  inv := coequalizer.desc (extendπ φ M) (by
    change ((β_ S R).hom ≫ γ[R,((comap φ).obj (regular S)).X]) ▷ M.X ≫
        extendπ φ M = _
    rw [restrictedRegular_rightAction φ]
    exact extendπ_condition φ M)
  hom_inv_id := by
    apply coequalizer.hom_ext
    simp only [extendDescHom, extendπ, tensorObjπ, coequalizer.π_desc_assoc]
    erw [coequalizer.π_desc, Category.comp_id]
    rfl
  inv_hom_id := by
    apply coequalizer.hom_ext
    simp only [extendDescHom, extendπ, tensorObjπ, coequalizer.π_desc_assoc]
    erw [coequalizer.π_desc, Category.comp_id]
    rfl

noncomputable def extendForgetTensorIso :
    extendScalars φ ⋙ forget S ≅
      tensorLeft ((comap φ).obj (regular S)) ⋙ forget R :=
  NatIso.ofComponents (extendForgetTensorObjIso φ) (by
    intro M N f
    apply (cancel_epi (extendπ φ M)).1
    simp [extendForgetTensorObjIso, extendπ_extendScalarsMap_assoc,
      tensorObjπ_whiskerLeft]
    rfl)
```

The enclosing `@[expose] public section` exports the definitions and their bodies. In the item,
all six remaining references to the duplicate names are replaced with references to these
shared definitions: the two finite-limit transfer lemmas use `extendForgetTensorIso`, and
`restrictExtendTensorIso` and `extendUnit_scalarEndo_tensor` use `extendForgetTensorObjIso`.
No extra import is needed: the existing `ChangeOfCoefficients` import supplies this module.

## Users

The source-only downstream listing has 31 consumers. Exact-name searches in the repository
find only the existing internal uses in `DerivedExtendScalars`; the item introduces the new
external uses listed above. All consumers retain the same previous API and mathematical
meaning. Holders below come from the local claims snapshot.

| module | group holding it | effect |
| --- | --- | --- |
| `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars` | unclaimed | Expose existing tensor isomorphisms; types and bodies unchanged. |
| `Sheaf.AlgebraicGeometry.CondensedConstructibleSerre` | B3 | No edit required; all existing public signatures and definitions unchanged. |
| `Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality` | B3 | No edit required; all existing public signatures and definitions unchanged. |
| `Sheaf.Paper.CondensedCoefficientComparisons` | unclaimed | No edit required; all existing public signatures and definitions unchanged. |
| `Sheaf.Paper.CondensedFinitePresentationDescent` | B3 | No edit required; all existing public signatures and definitions unchanged. |
| `Sheaf.Paper.CondensedFlatCoefficientCalculus` | A4 | No edit required; all existing public signatures and definitions unchanged. |
| `Sheaf.Paper.CondensedOpenClosedRecollement` | D3 | No edit required; all existing public signatures and definitions unchanged. |
| `Sheaf.Paper.CondensedPointBasisEvaluation` | D3 | No edit required; all existing public signatures and definitions unchanged. |
| `Sheaf.Paper.CondensedQbarBaseChangeCompatibility` | unclaimed | No edit required; all existing public signatures and definitions unchanged. |
| `Sheaf.Paper.CondensedQbarComparisons` | unclaimed | No edit required; all existing public signatures and definitions unchanged. |
| `Sheaf.Paper.CondensedQbarExchangeEquality` | A3 | No edit required; all existing public signatures and definitions unchanged. |
| `Sheaf.Paper.CondensedQbarLfpLocalTriviality` | C2 | No edit required; all existing public signatures and definitions unchanged. |
| `Sheaf.Paper.CondensedQcqsPushforwardContinuity` | D3 | No edit required; all existing public signatures and definitions unchanged. |
| `Sheaf.Paper.CondensedSheafExtContinuity` | C4 | No edit required; all existing public signatures and definitions unchanged. |
| `Sheaf.Paper.GeometricFieldProEtaleEvaluation` | D3 | No edit required; all existing public signatures and definitions unchanged. |
| `Sheaf.Paper.ProfinitePointPullback` | D2 | No edit required; all existing public signatures and definitions unchanged. |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp` | A2 | No edit required; all existing public signatures and definitions unchanged. |
| `TargetsCheck` | unclaimed | No edit required; all existing public signatures and definitions unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport` | unclaimed | No edit required; all existing public signatures and definitions unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs` | unclaimed | No edit required; all existing public signatures and definitions unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs` | unclaimed | No edit required; all existing public signatures and definitions unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper` | unclaimed | No edit required; all existing public signatures and definitions unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients` | unclaimed | No edit required; all existing public signatures and definitions unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility` | E4 | Remove both duplicate definitions and reuse the two shared tensor isomorphisms. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | B2 | No edit required; all existing public signatures and definitions unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` | E4 | No edit required; all existing public signatures and definitions unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek` | unclaimed | No edit required; all existing public signatures and definitions unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek` | unclaimed | No edit required; all existing public signatures and definitions unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar` | unclaimed | No edit required; all existing public signatures and definitions unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek` | unclaimed | No edit required; all existing public signatures and definitions unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs` | unclaimed | No edit required; all existing public signatures and definitions unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs` | unclaimed | No edit required; all existing public signatures and definitions unchanged. |

## Status

landed 20261015T184346-L-858739 2026-10-15 (merge of deliver/E4/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility)
