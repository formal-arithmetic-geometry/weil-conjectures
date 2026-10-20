# CartesianChartExchangeCore duplicate retirement

## Reason

This module is a listed retirement item in coord/retire-items.tsv, authorized by
coord/changes/retire-sheaf-twins-20261020.md. It contains zero holes and exactly
three private lemmas: single_source, single_restriction and square_comp. Their
signatures and complete proofs agree with the upstream twin, token for token
when whitespace is ignored. The upstream implementation supplies every use.

## Old

The duplicate's declarations and proofs are:

```lean
private lemma single_source {S Y Z : Scheme.{u}} (a : Z ⟶ Y) (h : Y ⟶ S)
    (h' : Z ⟶ S) (w : h' = a ≫ h)
    (M : Sheaf S.smallEtaleTopology A) :
    (DerivedCategory.Plus.singleFunctor _ 0).map
        ((upperStarComp A a h h' w).hom.app M) ≫
      (((a)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _ =
    (((h')^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.app M ≫
      (upperStarCompDerivedPlus A a h h' w).hom.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M) ≫
      D+((a)^*[A]).map
        ((((h)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app M) := by
  apply (cancel_epi
    ((((h')^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app M)).1
  simp only [Category.assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc, Category.comp_id]
  rw [← reassoc_of% (comp_single A a h h' w M)]
  simp only [Functor.comp_obj, Category.assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc,
    Category.comp_id]

private lemma single_restriction {S Y Z : Scheme.{u}} (a : Z ⟶ Y) (h : Y ⟶ S)
    (h' : Z ⟶ S) (w : h' = a ≫ h)
    (M : Sheaf S.smallEtaleTopology A) :
    (((a)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        ((upperStarComp A a h h' w).inv.app M) =
    D+((a)^*[A]).map
        ((((h)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.app M) ≫
      (upperStarCompDerivedPlus A a h h' w).inv.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M) ≫
      (((h')^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app M := by
  apply (cancel_mono
    ((((h')^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.app M)).1
  simpa only [Functor.comp_obj, Category.assoc, Iso.hom_inv_id_app, Category.comp_id] using
    comp_single_inv A a h h' w M

private lemma square_comp {B T T' Z Z' : Scheme.{u}}
    (t : Z' ⟶ Z) (p : Z ⟶ T) (p' : Z' ⟶ T') (b : T' ⟶ T)
    (sq : CommSq t p' p b) (a : T ⟶ B) (a' : T' ⟶ B) (ha : a' = b ≫ a)
    (s : Z ⟶ B) (hs : s = p ≫ a) (s' : Z' ⟶ B) (hs' : s' = p' ≫ a')
    (M : DerivedCategory.Plus (Sheaf B.smallEtaleTopology A)) :
    D+((p')^*[A]).map
        ((upperStarCompDerivedPlus A b a a' ha).hom.app M) ≫
      (pullbackSquareComparison A sq).hom.app
        (D+((a)^*[A]).obj M) ≫
      D+((t)^*[A]).map
        ((upperStarCompDerivedPlus A p a s hs).inv.app M) =
    (upperStarCompDerivedPlus A p' a' s' hs').inv.app M ≫
      (upperStarCompDerivedPlus A t s s'
        (by rw [hs', ha, ← Category.assoc p' b a, ← sq.w, Category.assoc, ← hs])).hom.app M := by
  let d := t ≫ p
  have hd : d = p' ≫ b := sq.w
  have hds : s' = d ≫ a := by rw [hs', ha, ← Category.assoc p' b a, ← hd]
  have h₁ := NatTrans.congr_app (upperStarCompDerivedPlus_assoc
    A t p a d s s' rfl hs hds) M
  have h₂ := NatTrans.congr_app (upperStarCompDerivedPlus_assoc
    A p' b a d a' s' hd ha hds) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h₁ h₂
  dsimp only [d] at h₁ h₂ hd hds
  rw [pullbackSquareComparison_eq]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  apply (cancel_epi
    ((upperStarCompDerivedPlus A p' a' s' hs').hom.app M)).1
  simp only [Category.assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc, Category.comp_id]
  rw [reassoc_of% h₂]
  simp only [Functor.comp_obj, Category.assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc,
    Category.comp_id]
  rw [← reassoc_of% h₁]
  simp only [← Functor.map_comp, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.comp_id]

```

The three direct consumers import:

```lean
import all Sheaf.AlgebraicGeometry.CartesianChartExchangeCore
```

## New

The duplicate is withdrawn through deleted.txt. The three direct consumers import:

```lean
import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeCore
```

The upstream three private lemmas, with precisely the old signatures and proofs,
remain unchanged. The replacement is a private proof import and changes no public
signature, public import, definition, theorem statement, target or unit route.
No DAG node or quarantined module references the duplicate, so no node attachment
or dependency update is needed.

## Users

The table includes all transitive importers returned by downstream.py, plus the
retired item. All consumers are unclaimed in the coordination snapshot. Only the
three direct importers change; each changes exactly its Core import line.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeCore | C3 | Withdraw the duplicate; retain upstream implementation. |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeAdjunction | unclaimed | Migrate private proof import; declarations and proofs unchanged. |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeComparison | unclaimed | Unchanged; validated against migrated consumers. |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeEvaluation | unclaimed | Unchanged; validated against migrated consumers. |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeSource | unclaimed | Migrate private proof import; declarations and proofs unchanged. |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeTransport | unclaimed | Migrate private proof import; declarations and proofs unchanged. |
| Sheaf.AlgebraicGeometry.CartesianChartLiftCoherence | unclaimed | Unchanged; validated against migrated consumers. |
| Sheaf.AlgebraicGeometry.CartesianChartLiftNaturality | unclaimed | Unchanged; validated against migrated consumers. |
| Sheaf.AlgebraicGeometry.CartesianChartLiftRawNaturality | unclaimed | Unchanged; validated against migrated consumers. |

All eight consumers are checked individually through lcompile.py. The import
closure audit introduces no new Sheaf/WeilConjectures twin pairs. The three Lift
consumers already had pairs for five other Exchange helpers; retirement removes
the Core pair without adding any. The five other consumers have no twin pairs.

## Status

landed 20261020T161730-L-3528944 2026-10-20 (merge of deliver/C3/Sheaf.AlgebraicGeometry.CartesianChartExchangeCore)
