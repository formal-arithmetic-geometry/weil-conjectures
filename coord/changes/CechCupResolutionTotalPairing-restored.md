# AlgebraicGeometry.Scheme.Modules.cupCechResolution_total_pairing

## Reason

Restore the two modules absent after the earlier rollback. Both are new declarations
relative to this delivery baseline. No existing statement or definition is changed.
The total pairing is constructed from the uniquely characterized sheaf cup product;
the beta-axis compatibility is the remaining named proof obligation.

## Old

Neither declaration nor either module exists in the current baseline.

## New

```lean
theorem cupCechResolution_beta_class_pairing {X : Scheme.{v}} {ι : Type v}
    (U : ι → X.Opens) {F G : X.Modules} (D : CupResolutionPairing F G)
    (A : CupCechResolutionComparison U D.left)
    (B : CupCechResolutionComparison U D.right)
    (C : CupCechResolutionComparison U D.target) (p q : ℕ)
    (cup : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F →ₗ[Γ(X, ⊤)]
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj G →ₗ[Γ(X, ⊤)]
        (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).obj
          (@id X.Modules (F ⊗ G)))
    (hcup : IsModuleCupProduct F G p q cup)
    (a : (((cechComplexFunctor U).obj F.presheafModuleCat).sc
      p).moduleCatLeftHomologyData.K)
    (b : (((cechComplexFunctor U).obj G.presheafModuleCat).sc
      q).moduleCatLeftHomologyData.K)
    (c : (((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).sc
      (p + q)).moduleCatLeftHomologyData.K)
    (hc : c.val = cechCupCochain U F G p q a.val b.val) :
    cup ((A.iso p).inv (HomologicalComplex.homologyMap A.beta p (cupCycleClass _ p a)))
      ((B.iso q).inv (HomologicalComplex.homologyMap B.beta q (cupCycleClass _ q b))) =
        (C.iso (p + q)).inv
          (HomologicalComplex.homologyMap C.beta (p + q) (cupCycleClass _ (p + q) c))
```

```lean
theorem cupCechResolution_total_pairing {X : Scheme.{v}} {ι : Type v}
    (U : ι → X.Opens) {F G : X.Modules} (D : CupResolutionPairing F G)
    (A : CupCechResolutionComparison U D.left)
    (B : CupCechResolutionComparison U D.right)
    (C : CupCechResolutionComparison U D.target) (p q : ℕ) :
    ∃ t : ((cupCechDouble U D.left.K).total (ComplexShape.up ℕ)).homology p →ₗ[Γ(X, ⊤)]
      ((cupCechDouble U D.right.K).total (ComplexShape.up ℕ)).homology q →ₗ[Γ(X, ⊤)]
        ((cupCechDouble U D.target.K).total (ComplexShape.up ℕ)).homology (p + q),
      (∀ (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
        (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
        (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K),
        c.val = D.pair p q ⊤ a.val b.val →
          t (HomologicalComplex.homologyMap A.alpha p (cupCycleClass _ p a))
              (HomologicalComplex.homologyMap B.alpha q (cupCycleClass _ q b)) =
            HomologicalComplex.homologyMap C.alpha (p + q) (cupCycleClass _ (p + q) c)) ∧
      (∀ (a : (((cechComplexFunctor U).obj F.presheafModuleCat).sc
          p).moduleCatLeftHomologyData.K)
        (b : (((cechComplexFunctor U).obj G.presheafModuleCat).sc
          q).moduleCatLeftHomologyData.K)
        (c : (((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).sc
          (p + q)).moduleCatLeftHomologyData.K),
        c.val = cechCupCochain U F G p q a.val b.val →
          t (HomologicalComplex.homologyMap A.beta p (cupCycleClass _ p a))
              (HomologicalComplex.homologyMap B.beta q (cupCycleClass _ q b)) =
            HomologicalComplex.homologyMap C.beta (p + q) (cupCycleClass _ (p + q) c))
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CechCupResolutionTotalPairing | P2 | Restored theorem; imports the beta theorem for its proof. |
| Sheaf.Paper.CechCupResolutionBetaClassPairing | P2 | Restored beta compatibility theorem; one named sorry. |

No baseline Lean module imports or references either absent declaration (checked
with rg on lean/). There are no forced adaptations or changed target definitions.

## Status

landed 20261014T001728-L-2553117 2026-10-14 (merge of deliver/P2/Sheaf.Paper.CechCupResolutionTotalPairing)
