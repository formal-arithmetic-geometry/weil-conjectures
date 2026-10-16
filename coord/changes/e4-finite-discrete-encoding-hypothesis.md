# AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteExchange_comparison

## Reason

The shared item was proved by A3 immediately before this assignment began, and has zero
local holes. Its statement nevertheless retained an additional `hEncoding` hypothesis.
The already-proved `CategoryTheory.constantInternalModuleSheaf_equivalence` supplies
exactly this witness for every scheme. Construct it inside the comparison theorem,
so the finite discrete comparison needs only its stated geometric and coefficient data.
This is a strict strengthening of an intermediate theorem, not a change to a target.

## Old

```lean
theorem finiteDiscreteExchange_comparison (hB : (ℓ : B) = 0) (sq : CommSq g' f' f g) (N : ProEtale.BoundedConstructible (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X)) (hEncoding : ∀ T : Scheme.{u}, ∃ G : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (Scheme.ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} B) : RingCat.{u + 1}))) ⥤ Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} B)), G.IsEquivalence ∧ Nonempty (G ⋙ sheafCompose (Scheme.ProEt.topology T) (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1}) ≅ Mod.forget (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (Scheme.ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} B) : RingCat.{u + 1}))))) : ∃ (F : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} B))) ⥤ DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y') Ab.{u + 1}) (condensedRingObj (Profinite.continuousMapRingObj.{u} B) Y'))) (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} B)))), Nonempty (Arrow.mk ((boundedConstructibleBaseChange (Profinite.continuousMapRingObj.{u} B) ℓ k sq).app N).hom ≅ Arrow.mk (F.map ((Etale.baseChange (ModuleCat.{u + 1} (ULift.{u + 1} B)) sq).app L)))
```

## New

```lean
theorem finiteDiscreteExchange_comparison (hB : (ℓ : B) = 0) (sq : CommSq g' f' f g) (N : ProEtale.BoundedConstructible (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X)) : ∃ (F : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} B))) ⥤ DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y') Ab.{u + 1}) (condensedRingObj (Profinite.continuousMapRingObj.{u} B) Y'))) (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} B)))), Nonempty (Arrow.mk ((boundedConstructibleBaseChange (Profinite.continuousMapRingObj.{u} B) ℓ k sq).app N).hom ≅ Arrow.mk (F.map ((Etale.baseChange (ModuleCat.{u + 1} (ULift.{u + 1} B)) sq).app L)))
```

## Users

The complete transitive list comes from
`tools/downstream.py Sheaf.Paper.FiniteDiscreteExchangeComparison --uses finiteDiscreteExchange_comparison`.
Only `IntegralFiniteExchangeComparison` calls this declaration. All other downstream
modules use its consumer with the same signature as before. No definition changes, so
no target interpretation changes or statement review reopening is required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | E4 | Statement strengthened by removing the proved encoding hypothesis. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | No source change; its statements and definitions retain their meaning. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Drop the final encoding argument and its proof-only import; all declaration signatures unchanged. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | No source change; its statements and definitions retain their meaning. |
| TargetsCheck | unclaimed | No source change; its statements and definitions retain their meaning. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No source change; its statements and definitions retain their meaning. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No source change; its statements and definitions retain their meaning. |

The two adapted modules compile together. The original integral consumer no longer
compiles with the strengthened comparison interface because it supplies an extra argument.
Its adaptation removes only that argument and its unused proof-only import.
The constant-ring equivalence and all other modules keep their existing implementations.

## Status

landed 20261016T064222-L-582365 2026-10-16 (merge of deliver/E4/Sheaf.Paper.FiniteDiscreteExchangeComparison)
