# CategoryTheory.Abelian.Ext.mapExactFunctor_comp_mk₀_eq

## Reason

Upstream review #1424 asks for the general canonical composition lemma instead of a duplicate. Prior landed repairs removed exactFunctorCompositionComparison and repointed all callers. The cited source declaration is absent on this baseline; adding a public declaration to the unheld source module is not a forced adaptation. Generalize the existing canonical declaration in the held module to independent Ext universes, matching the universe flexibility of Ext.mapExactFunctor. This is a genuine removal of an unnecessary restriction, with no new theorem or alias. No EnoughInjectives assumption is needed.

## Old

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

## New

```lean
theorem mapExactFunctor_comp_mk₀_eq
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasExt.{w} C] [HasExt.{w'} D] [HasExt.{w''} E]
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

Only the Ext universes are generalized. No target statement or definition changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AbelianRepresentableCohomologyMapNaturality | unclaimed | Existing calls specialize the independent universes; no edits required. |
| Sheaf.AlgebraicGeometry.Cohomology.InverseImageCohomologyComposition | unclaimed | Existing calls specialize the independent universes; no edits required. |
| Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial | unclaimed | Existing calls specialize the independent universes; no edits required. |
| Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyNatural | unclaimed | Existing calls specialize the independent universes; no edits required. |
| Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyPullback | unclaimed | Existing calls specialize the independent universes; no edits required. |
| Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalOpenToOpenCycle | unclaimed | Existing calls specialize the independent universes; no edits required. |
| Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackComposition | unclaimed | Existing calls specialize the independent universes; no edits required. |
| Sheaf.AlgebraicGeometry.ScalarExtCupInverseImageSecond | unclaimed | Existing calls specialize the independent universes; no edits required. |
| Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullbackCompositionPointwise | unclaimed | Existing calls specialize the independent universes; no edits required. |
| Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison | unclaimed | Existing calls specialize the independent universes; no edits required. |

The holder column records no adaptation claim: no downstream file is changed by this delivery.

## Status

landed 20261014T054053-L-2107695 2026-10-14 (merge of deliver/R2/Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison)
