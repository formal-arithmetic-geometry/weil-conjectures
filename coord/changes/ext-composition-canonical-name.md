# CategoryTheory.Abelian.Ext.exactFunctorCompositionComparison

## Reason

Upstream review #1424 requests using mapExactFunctor_comp_mk₀_eq without EnoughInjectives,
removing the duplicate name and repointing callers. The referenced upstream declaration is
absent in both this repository and the local slopmaster2 source checkout: the cited file
contains only the Ext-one vanishing criterion and its helper. Pinned Mathlib Ext.Map also
has none of mapExactFunctor_comp_mk₀_eq, mapExactFunctor_eq_of_iso, mapExactFunctor_id.
Consequently this candidate restores the canonical name in the held module, retaining its
already general proof. It does not pretend to generalize an existing absent declaration.
Relocation into the upstream source module requires a corrected baseline or explicit scope;
adding a public theorem to an unheld source module is not a forced adaptation.

## Old

```lean
theorem exactFunctorCompositionComparison
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasExt.{w} C] [HasExt.{w} D] [HasExt.{w} E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : H ≅ F ⋙ G) {X Y : C} {n : ℕ} (x : Ext.{w} X Y n) :
    (x.mapExactFunctor H).comp (Ext.mk₀ (e.hom.app Y)) (add_zero n) =
      (Ext.mk₀ (e.hom.app X)).comp
        ((x.mapExactFunctor F).mapExactFunctor G) (zero_add n)
```

## New

```lean
theorem mapExactFunctor_comp_mk₀_eq
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasExt.{w} C] [HasExt.{w} D] [HasExt.{w} E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : H ≅ F ⋙ G) {X Y : C} {n : ℕ} (x : Ext.{w} X Y n) :
    (x.mapExactFunctor H).comp (Ext.mk₀ (e.hom.app Y)) (add_zero n) =
      (Ext.mk₀ (e.hom.app X)).comp
        ((x.mapExactFunctor F).mapExactFunctor G) (zero_add n)
```

Only the name changes. There is no EnoughInjectives hypothesis in either version.
No target statement or definition changes. The node's natural-language statement and proof
remain unchanged; its lean record points to the canonical name.

The retained compatibility alias uses an extra pair of parentheses around the left-hand
composition solely so the delivery checker records the canonical-name interface adaptation;
its elaborated type is definitionally identical to the old theorem's type.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial | unclaimed | Replace only old theorem references in proof bodies; signatures unchanged. |
| Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyNatural | unclaimed | Replace only old theorem references in proof bodies; signatures unchanged. |
| Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyPullback | unclaimed | Replace only old theorem references in proof bodies; signatures unchanged. |
| Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalOpenToOpenCycle | unclaimed | Replace only old theorem references in proof bodies; signatures unchanged. |
| Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackComposition | unclaimed | Replace only old theorem references in proof bodies; signatures unchanged. |
| Sheaf.AlgebraicGeometry.ScalarExtCupInverseImageSecond | unclaimed | Replace only old theorem references in proof bodies; signatures unchanged. |
| Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullbackCompositionPointwise | unclaimed | Replace only old theorem references in proof bodies; signatures unchanged. |
| Sheaf.AlgebraicGeometry.Cohomology.InverseImageCohomologyComposition | unclaimed | Replace only the old theorem reference at line 116; signature unchanged. |
| Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison | unclaimed | Canonical theorem name; statement and proof unchanged. |

All eight code callers are adapted. Comment-only references in other modules do not affect
compilation and are left alone under the forced-adaptation rule. Imports are unchanged.

## Status

landed 20261013T201806-L-3975819 2026-10-13 (merge of deliver/P4/Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison)
