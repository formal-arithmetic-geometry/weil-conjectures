# CategoryTheory.Mod.restrictedRegular_rightAction

## Reason

Repair the maintainer's returned duplicate-statement finding. The item had reproved this
private theorem under the name `rightAct_regular`. Expose the existing theorem for reuse,
remove the duplicate, and reuse the shared scalar/tensor construction. The H4 repair now
also removes `extendTensorIso` itself; the right-action theorem is used internally by the
shared `extendForgetTensorObjIso`.
`WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars` is unclaimed in the
local claims snapshot, so the authorized unclaimed-module rule permits this visibility edit.
There is no forced adaptation of a module held by another group.

## Old

Within the existing `CategoryTheory.Mod` namespace and variable context:

```lean
omit [Abelian C] [MonoidalPreadditive C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
  [IsCommMonObj R] in
private lemma restrictedRegular_rightAction :
    (β_ S R).hom ≫ γ[R,((comap φ).obj (regular S)).X] = S ◁ φ ≫ μ[S] := by
  change (β_ S R).hom ≫ φ ▷ S ≫ μ[S] = _
  rw [← BraidedCategory.braiding_naturality_right_assoc, IsCommMonObj.mul_comm]
```

## New

```lean
omit [Abelian C] [MonoidalPreadditive C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
  [IsCommMonObj R] in
/-- The right action on the restricted regular module is multiplication after scalar change. -/
lemma restrictedRegular_rightAction :
    (β_ S R).hom ≫ γ[R,((comap φ).obj (regular S)).X] = S ◁ φ ≫ μ[S] := by
  change (β_ S R).hom ≫ φ ▷ S ≫ μ[S] = _
  rw [← BraidedCategory.braiding_naturality_right_assoc, IsCommMonObj.mul_comm]
```

The enclosing `@[expose] public section` makes the theorem reusable by importers. Neither its
binders, statement or proof change. The item removes `rightAct_regular`; the shared
`extendForgetTensorObjIso` uses this theorem for its two coequalizer compatibility proofs.
The new record `E4-visibility-reuse-extend-tensor-isos.md` documents the further visibility
changes required by H4. Its existing public import of `ChangeOfCoefficients` already imports
`DerivedExtendScalars`, so no import is added. This changes no target's meaning.

## Users

`tools/downstream.py` reports the following 31 downstream modules. Its exact-name search
finds only the two existing internal uses and declaration in `DerivedExtendScalars`;
these continue to elaborate. The item now uses the shared tensor isomorphisms, whose
construction uses this theorem. Exposing a theorem
preserves the old public API, so all other consumers require no edit or statement review.
The holders below are the local claims snapshot at repair time.

| module | group holding it | effect |
| --- | --- | --- |
| `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars` | unclaimed | Expose existing proved lemma; statement and proof unchanged. |
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
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility` | E4 | Remove duplicate helper and reuse the shared scalar/tensor construction. |
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
