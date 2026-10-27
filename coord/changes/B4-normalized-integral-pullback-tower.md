# WeilConjectures.IntegralAmbient.pullTowerModel

## Reason

Close the sole remaining hole using normalized adjunctions. Profiling the completed combined
module showed 81.4 seconds. An abstract composite-unit extensionality lemma avoids repeatedly
unfolding completed ring limits, reducing the formerly expensive restricted-map argument.
The remaining self-contained pullback presentation and its proved tower comparison are isolated
in `Sheaf.Paper.NormalizedIntegralPullbackTower`; each delivered file must compile within 60 s.
This follows the explicit worker brief of 2026-10-26, step 3a, after improving the slow argument.

## Old

In `Sheaf.Paper.IntegralAmbientOperationModels`, with proof `by sorry`:

```lean
theorem pullTowerModel {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ∃! b : pullTower l E f ≅ integralOperationsPullbackTowerFunctor l E f,
      ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) (i : ℤ)
        (V : Y.ProEt) (a : (integralCoefficientCommRingSheaf l E X n).obj.obj
          (op ((Scheme.proEtaleBaseChange f).obj V))) (x : (P.X i).val.obj (op V)),
        (((b.hom.app P).app (op n)).f i).val.app
            (op ((Scheme.proEtaleBaseChange f).obj V))
          (IntegralOnSlice.generator l E X none n ((pull l E f).obj (P.X i))
            (op ((Scheme.proEtaleBaseChange f).obj V)) a (pullSection l E f (P.X i) V x)) =
          finitePullSection l E f n P i V a x
```

## New

The identical declaration is proved in `Sheaf.Paper.NormalizedIntegralPullbackTower` and publicly
reexported by the item module:

```lean
theorem pullTowerModel {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ∃! b : pullTower l E f ≅ integralOperationsPullbackTowerFunctor l E f,
      ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) (i : ℤ)
        (V : Y.ProEt) (a : (integralCoefficientCommRingSheaf l E X n).obj.obj
          (op ((Scheme.proEtaleBaseChange f).obj V))) (x : (P.X i).val.obj (op V)),
        (((b.hom.app P).app (op n)).f i).val.app
            (op ((Scheme.proEtaleBaseChange f).obj V))
          (IntegralOnSlice.generator l E X none n ((pull l E f).obj (P.X i))
            (op ((Scheme.proEtaleBaseChange f).obj V)) a (pullSection l E f (P.X i) V x)) =
          finitePullSection l E f n P i V a x
```

The completed coefficient map, push, pull, adjunction, additive instances, pullComplex,
pullSection, finitePullSection and pullTower move with it. Their names, signatures, attributes
and definition bodies are unchanged. Only their module location and blueprint attachment move.
The original public imports stay and the support module is publicly imported so definitions
in the item module continue to use precisely the same constants. No target or adopted source
module changes, and no mathematical definition changes meaning. All other existing proofs
and definitions remain textually identical.

## Users

`tools/downstream.py ... --uses pullTowerModel` reports the item and the direct textual users
OrdinaryIntegralPullbackConstruction and QcqsCompletionOrdinaryModels. The full import closure
has 801 downstream modules. Below are all nine direct importers; the unchanged public
interface propagates through them. Their original files are compiled against the delivery,
and all nine compiled successfully. The unchanged validation copies were removed from the packet.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralAmbientOperationModels | B4 | Reexports the unchanged declarations; derived and tensor proofs unchanged. |
| Sheaf.Paper.IntegralOperationRoosEffectivity | unclaimed | Same declarations through public reexport; original importer validation. |
| Sheaf.Paper.OrdinaryIntegralPullbackConstruction | unclaimed | Same declarations through public reexport; original importer validation. |
| Sheaf.Paper.PodReindexingRoosComparison | unclaimed | Same declarations through public reexport; original importer validation. |
| Sheaf.Paper.PodReindexingRoosShiftCompatibility | unclaimed | Same declarations through public reexport; original importer validation. |
| Sheaf.Paper.PointIntegralTensorChain | unclaimed | Same declarations through public reexport; original importer validation. |
| Sheaf.Paper.QcqsCompletionOrdinaryModels | unclaimed | Same declarations through public reexport; original importer validation. |
| Sheaf.Paper.ZlFiniteIntegralFibreReconstruction | unclaimed | Same declarations through public reexport; original importer validation. |
| Sheaf.TraceFormula.IsomorphismRoosUnitCancellation | unclaimed | Same declarations through public reexport; original importer validation. |
| Sheaf.TraceFormula.StrictQuotientCompletionUnit | unclaimed | Same declarations through public reexport; original importer validation. |

## Status

landed 20261026T130259-L-3445421 2026-10-26 (merge of deliver/B4/Sheaf.Paper.IntegralAmbientOperationModels)
