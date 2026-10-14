# CategoryTheory.Abelian.Ext.exactFunctorCompositionComparison

## Reason

Complete upstream duplicate repair #1424, still listed in coord/repairs.txt. The earlier canonical-name repair retained a compatibility alias and the current eight code callers still use it. Remove this second theorem name and repoint all code callers to the already proved canonical theorem. The existing general proof needs no EnoughInjectives assumption and is preserved verbatim.

The cited upstream generalization cannot be performed literally on this baseline: `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Map` contains only the Ext-one vanishing criteria, and pinned Mathlib Ext.Map contains no theorem named `mapExactFunctor_comp_mk₀_eq`. The canonical theorem therefore stays in the held module; no theorem is invented in an unheld upstream module.

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
    ((x.mapExactFunctor H).comp (Ext.mk₀ (e.hom.app Y)) (add_zero n)) =
      (Ext.mk₀ (e.hom.app X)).comp
        ((x.mapExactFunctor F).mapExactFunctor G) (zero_add n)
```

## New

The compatibility alias is removed. Every proof caller instead uses the existing canonical declaration, whose signature and proof are unchanged:

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

No target statement or definition changes. No new statements, definitions or holes are added; the mathematical interface is consolidated under its canonical name.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Cohomology.InverseImageCohomologyComposition | unclaimed | Forced theorem-reference substitution on lines 116; signatures unchanged. |
| Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial | unclaimed | Forced theorem-reference substitution on lines 57; signatures unchanged. |
| Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyNatural | unclaimed | Forced theorem-reference substitution on lines 72; signatures unchanged. |
| Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyPullback | unclaimed | Forced theorem-reference substitution on lines 69, 73; signatures unchanged. |
| Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalOpenToOpenCycle | unclaimed | Forced theorem-reference substitution on lines 128; signatures unchanged. |
| Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackComposition | unclaimed | Forced theorem-reference substitution on lines 78; signatures unchanged. |
| Sheaf.AlgebraicGeometry.ScalarExtCupInverseImageSecond | unclaimed | Forced theorem-reference substitution on lines 76; signatures unchanged. |
| Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullbackCompositionPointwise | unclaimed | Forced theorem-reference substitution on lines 215; signatures unchanged. |
| Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison | G3 | Remove deprecated compatibility alias; canonical theorem unchanged. |

These are all nine declaration users reported by tools/downstream.py --uses exactFunctorCompositionComparison (including the defining module). Other downstream modules do not use the removed declaration. Comment-only references in `Sheaf.AlgebraicGeometry.Cohomology.MayerVietorisExtFunctorSquare`, `Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalOpenToOpen` and `Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyPullback` are left unchanged.

## Status

landed 20261014T045610-L-1573248 2026-10-14 (merge of deliver/G3/Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison)
