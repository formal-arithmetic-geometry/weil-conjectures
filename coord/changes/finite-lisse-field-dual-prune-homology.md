# AlgebraicGeometry.Etale.sitePerfect_fieldDual_homology

## Reason

Withdraw the now unnecessary site-perfect dual-homology auxiliary theorem. Its sole
parent is globally bounded, and the adopted source library already proves its full
finite-lisse duality conclusion by truncation devissage. Deliver the actual replacement
parent proof together with both DAG route updates. This removes an unnecessary stronger
locally bounded obligation rather than handing its proof to another worker.

The adapted parent `Sheaf.AlgebraicGeometry.FiniteLisseFieldDual` is unclaimed.
No source-library module, target, public signature, definition body or public import changes.

## Old

```lean
theorem sitePerfect_fieldDual_homology
    (ℓ : ℕ) [Fact ℓ.Prime] (T : Scheme.{u})
    (C : DerivedCategoryModule (ULift.{u + 1} (ZMod ℓ)) T) (hC : DerivedCategory.IsSitePerfect C) :
    ∀ q : ℤ, Nonempty
      ((_root_.DerivedCategory.homologyFunctor _ q).obj
          (((derivedHom (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) T).obj (op C)).obj
            (constantComplex (ULift.{u + 1} (ZMod ℓ)) T)) ≅
        (ihom ((_root_.DerivedCategory.homologyFunctor _ (-q)).obj C)).obj
          (𝟙_ (Sheaf T.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))))) 
```

Its only external textual use is the proof of `finiteLisseFieldDual`, which first
constructed site-perfectness using `finiteLisseField_sitePerfect`.

## New

The item module is withdrawn, with no replacement declaration. The unchanged parent
`finiteLisseFieldDual` converts its existing bounds into `IsGE` and `IsLE`, and applies:

- `isFiniteLocallyConstantSheaf_homology_coefficientDual` for its first two conclusions;
- `isIso_coefficientDualComparison_of_isFiniteLocallyConstantSheaf` for its third.

Both theorems are fully proved in the adopted
`WeilConjectures.SixFunctors.Etale.Derived.LisseFieldDual` module. The canonical comparison
maps are definitionally equal, so no comparison definition is changed. Both removed
Sheaf imports were proof-only. The two private helpers `dualPullback_isIso_of_exactPairing`
and `finiteLisseDualPullbackComparison_isIso`, used only by the old proof, are removed with
the proof-only `Perfect.SitePerfect` import they needed (reviewer fix); the proof docstring
of `finiteLisseFieldDual` now describes the new route.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.FiniteLisseFieldDualHomology --uses
sitePerfect_fieldDual_homology` lists the item and its parent as the only textual users;
its transitive importer list additionally contains `SmoothGenericDirectImage`.
The DAG scan finds only `lem-fin-lisse-field-dual` as a parent. The unit's realized arrays
are empty. Searches of `quarantine/`, `dag/units/` and `coord/rework.tsv` find no further use.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteLisseFieldDualHomology | Q1 | Withdrawn; one unneeded hole removed. |
| Sheaf.AlgebraicGeometry.FiniteLisseFieldDual | unclaimed | Same signature and comparison map; proof uses the proved adopted bounded theorem. |
| Sheaf.AlgebraicGeometry.SmoothGenericDirectImage | B7 | Unchanged consumer compiled against the replacement parent. |

## Status

landed 20261023T170058-L-2063293 2026-10-23 (merge of deliver/Q1/Sheaf.AlgebraicGeometry.FiniteLisseFieldDualHomology)
