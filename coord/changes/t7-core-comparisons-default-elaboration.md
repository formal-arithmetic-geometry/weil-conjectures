# AlgebraicGeometry.openPullbackRestrictionIso_hom_app_eq_square_inv

## Reason

The rework row describes the old quarantine failure, but U9's restoration was already
landed before this claim. The current source compiles. Preserve that restoration and
all public reexports, replace the forward-square proof's reconstructed isomorphism
and two congrArg steps by Mathlib's Iso.hom_eq_inv on the two component isomorphisms,
and remove three unnecessary file-wide elaboration overrides. This changes the proof
and its elaboration configuration, not any comparison construction or public signature.
It does not claim a new mathematical hole closure or a new restoration.

## Old

```lean
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem openPullbackRestrictionIso_hom_app_eq_square_inv
    {X Y : Scheme.{u}} (g : X ⟶ Y) (P : X.Opens) (U : Y.Opens)
    (h : P ≤ g ⁻¹ᵁ U) (M : schemeDerivedCategory Y) :
    (openPullbackRestrictionIso g P U h).hom.app M =
      (singleComplexOpenPullbackSquareIso g U P (g.resLE U P h)
        (Scheme.Hom.resLE_comp_ι g h)).inv.app M := by
  have he : (openPullbackRestrictionIso g P U h).symm.app M =
      (singleComplexOpenPullbackSquareIso g U P (g.resLE U P h)
        (Scheme.Hom.resLE_comp_ι g h)).app M := by
    apply Iso.ext
    exact openPullbackRestrictionIso_inv_app_eq_square g P U h M
  have := congrArg Iso.symm he
  exact congrArg Iso.hom this
```

## New

The three overrides are absent; the complete module compiles with default settings.

```lean
theorem openPullbackRestrictionIso_hom_app_eq_square_inv
    {X Y : Scheme.{u}} (g : X ⟶ Y) (P : X.Opens) (U : Y.Opens)
    (h : P ≤ g ⁻¹ᵁ U) (M : schemeDerivedCategory Y) :
    (openPullbackRestrictionIso g P U h).hom.app M =
      (singleComplexOpenPullbackSquareIso g U P (g.resLE U P h)
        (Scheme.Hom.resLE_comp_ι g h)).inv.app M := by
  exact (Iso.hom_eq_inv ((openPullbackRestrictionIso g P U h).app M)
    ((singleComplexOpenPullbackSquareIso g U P (g.resLE U P h)
      (Scheme.Hom.resLE_comp_ι g h)).app M)).2
    (openPullbackRestrictionIso_inv_app_eq_square g P U h M).symm
```

## Users

`tools/downstream.py` finds zero live downstream modules, and its declaration-use
scan finds only the item. Seven direct consumers remain archived in quarantine;
they and the five DAG parents are still needed. The new proof has the identical
signature, universe and instance binders. No archived file is changed or withdrawn.
No target definition changes, so target-meaning review is not reopened.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreComparisons | T7 | proof uses Iso.hom_eq_inv; default elaboration |
| Sheaf.AlgebraicGeometry.PerfectOverlapNestedSiteCompatibility | quarantined | same four component theorems and source reexports |
| Sheaf.AlgebraicGeometry.PerfectOverlapStageTransport | quarantined | same constructor API and stage compatibility reexports |
| Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreTransport | quarantined | same constructor API |
| Sheaf.AlgebraicGeometry.PerfectOverlapProjectionCompositionComponent | quarantined | same constructor API |
| Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreOfData | quarantined | same constructor API |
| Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreCanonicalFamily | quarantined | same constructor API |
| Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreData | quarantined | same constructor API |

## Status

landed 20261021T170808-L-2761632 2026-10-21 (merge of deliver/T7/Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreComparisons)
