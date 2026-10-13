# CategoryTheory.sourceExtMap

## Reason
Relocate the public Ext comparison map alongside its compatibility theorem. Repair X-e672c requires a private Ext.Map import. With that import, the exposed definition body fails to elaborate: `Invalid field mapExtAddHom ... imported privately`. Keep the definition public with its unchanged type and body, but prevent body exposure using `@[no_expose]`; allow the item’s proofs to unfold it through a private `import all`.

## Old
Absent from the current repository baseline. In the earlier returned worker delivery, this declaration was in `Sheaf.CategoryTheory.DerivedSourceComparisonInjective`, with the same signature and (for the map) defining expression.

## New
Relocated to `Sheaf.CategoryTheory.DerivedSourceComparisonExtCompatibility`. Exact delivered declaration:

```lean
@[no_expose] noncomputable def sourceExtMap
    {C : Type u₁} {D : Type u₂} [Category.{v} C] [Category.{v} D]
    [Abelian C] [Abelian D] [HasExt.{v} C] [HasExt.{v} D]
    (V : C ⥤ D) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (L : C) (B : D) (a : B ⟶ V.obj L) (Y : C) (q : ℕ) :
    Abelian.Ext L Y q →+ Abelian.Ext B (V.obj Y) q :=
  ((Abelian.Ext.mk₀ a).precomp _ (zero_add q)).comp (V.mapExtAddHom L Y q)
```

## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.DerivedSourceComparisonInjective | B2 | Uses the relocated map in the dimension-shifting proof. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomMapInjective | unclaimed | Its existing injectivity dependency keeps the same public theorem signature; no adaptation is needed. |

## Status
landed 20261013T172650-L-2097784 2026-10-13 (merge of deliver/B2/Sheaf.CategoryTheory.DerivedSourceComparisonInjective)
