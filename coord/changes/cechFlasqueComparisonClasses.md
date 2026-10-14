# AlgebraicGeometry.Scheme.Modules.cechFlasqueComparisonClasses

## Reason

Restore the open-cover assumption of Stacks Tag 01EQ, Lemma 20.11.2. The split omitted it even though its proposed proof cancels the injective alpha homology map, whose invertibility theorem requires this assumption. This is an intermediate statement correction, not a change to a Challenge target. No counterexample to the unrestricted statement is asserted.

## Old

```lean
theorem cechFlasqueComparisonClasses {X : Scheme.{v}} {ι : Type v}
    (U : ι → X.Opens) {F : X.Modules} (D : CupAcyclicResolution F)
    (alpha : ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.K ⟶ (cupCechDouble U D.K).total (ComplexShape.up ℕ))
    (beta : (cechComplexFunctor U).obj F.presheafModuleCat ⟶
      (cupCechDouble U D.K).total (ComplexShape.up ℕ)) [QuasiIso alpha]
    (halpha : ∀ n : ℕ, alpha.f n = moduleCechZero U (D.K.X n) ≫
      (cupCechDouble U D.K).ιTotal (ComplexShape.up ℕ) n 0 n (by simp))
    (hbeta : ∀ n : ℕ, beta.f n =
      ((cechComplexFunctor U).map
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
          (D.augmentation.f 0).val)).f n ≫
      (cupCechDouble U D.K).ιTotal (ComplexShape.up ℕ) 0 n n (by simp)) :
    ∃ iso : ∀ n : ℕ, (RingedSpace.moduleCohomology X.toRingedSpace n).obj F ≅
      ((cupCechDouble U D.K).total (ComplexShape.up ℕ)).homology n,
      (∀ (n : ℕ)
        (z : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.K).sc n).moduleCatLeftHomologyData.K),
        (iso n).hom (D.class n z) =
          HomologicalComplex.homologyMap alpha n (cupCycleClass _ n z)) ∧
      (∀ (n : ℕ)
        (c : ((cechComplexFunctor U).obj F.presheafModuleCat).homology n ⟶
          (RingedSpace.moduleCohomology X.toRingedSpace n).obj F),
        IsModuleCechComparison U F n c →
        ∀ z : (((cechComplexFunctor U).obj F.presheafModuleCat).sc n).moduleCatLeftHomologyData.K,
          (iso n).hom (c (cupCycleClass _ n z)) =
            HomologicalComplex.homologyMap beta n (cupCycleClass _ n z))
```

## New

```lean
theorem cechFlasqueComparisonClasses {X : Scheme.{v}} {ι : Type v}
    (U : ι → X.Opens) (hU : iSup U = ⊤) {F : X.Modules} (D : CupAcyclicResolution F)
    (alpha : ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.K ⟶ (cupCechDouble U D.K).total (ComplexShape.up ℕ))
    (beta : (cechComplexFunctor U).obj F.presheafModuleCat ⟶
      (cupCechDouble U D.K).total (ComplexShape.up ℕ)) [QuasiIso alpha]
    (halpha : ∀ n : ℕ, alpha.f n = moduleCechZero U (D.K.X n) ≫
      (cupCechDouble U D.K).ιTotal (ComplexShape.up ℕ) n 0 n (by simp))
    (hbeta : ∀ n : ℕ, beta.f n =
      ((cechComplexFunctor U).map
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
          (D.augmentation.f 0).val)).f n ≫
      (cupCechDouble U D.K).ιTotal (ComplexShape.up ℕ) 0 n n (by simp)) :
    ∃ iso : ∀ n : ℕ, (RingedSpace.moduleCohomology X.toRingedSpace n).obj F ≅
      ((cupCechDouble U D.K).total (ComplexShape.up ℕ)).homology n,
      (∀ (n : ℕ)
        (z : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.K).sc n).moduleCatLeftHomologyData.K),
        (iso n).hom (D.class n z) =
          HomologicalComplex.homologyMap alpha n (cupCycleClass _ n z)) ∧
      (∀ (n : ℕ)
        (c : ((cechComplexFunctor U).obj F.presheafModuleCat).homology n ⟶
          (RingedSpace.moduleCohomology X.toRingedSpace n).obj F),
        IsModuleCechComparison U F n c →
        ∀ z : (((cechComplexFunctor U).obj F.presheafModuleCat).sc n).moduleCatLeftHomologyData.K,
          (iso n).hom (c (cupCycleClass _ n z)) =
            HomologicalComplex.homologyMap beta n (cupCycleClass _ n z))
```

The unused public import `Sheaf.Paper.CechFlasqueComparisonCore` is removed. A proof-only `import all Sheaf.AlgebraicGeometry.ModuleCechComparison` makes its already proved private restriction-naturality lemma available. The sole direct importer, `Sheaf.Paper.CechFlasqueResolutionComparison`, already imports CechCupResolutionComparisonData and Mathlib.Topology.Sheaves.Flasque itself; it compiles against the changed module. The computing data and all definitions are unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CechFlasqueComparisonClasses | M2 | Add the source's cover hypothesis and prove the theorem. |
| Sheaf.Paper.CechFlasqueResolutionComparison | unclaimed | Forced adaptation: pass its existing hU at the sole theorem application (line 54). Its signature and visibility are identical. |

All other transitive importers see the same public statements from CechFlasqueResolutionComparison; no target statement or definition changes. There are no DAG citers of the split node in stmt_deps or proof_deps.

## Status

landed 20261014T063820-L-2814586 2026-10-14 (merge of deliver/M2/Sheaf.Paper.CechFlasqueComparisonClasses)
