# IntegralPullbackCounitProjection source restoration

## Reason

The C4 split's node and Lean attachment remain, but its module was removed with
the reverted packet. There is no quarantine/rework row. V8's claim was released
at 2026-10-25T22:30:40Z as "done meanwhile" (coord/deliveries.log), although the
file is absent. It is now unclaimed. Restore the existing declaration, needed
by the assembly proof, rather than silently dropping its attachment or creating
a duplicate statement. The remaining proof is exactly the existing finite map
calculation; the main module separately constructs the comparison and proves
invertibility. No data definition uses a new unproved existence witness.

## Old

The live module is absent. The preserved node
lem-pod-integral-pullback-counit-projection records this signature:

```lean
theorem integralPullbackCounitProjection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (S : CoefficientDerivedSystemCalculus l E Y)
    (T : CoefficientDerivedSystemCalculus l E X)
    (ρ : IntegralComparisonRoosModel l E X)
    (M : IntegralComparisonPullbackModel l E f S ρ)
    (K : DerivedCategory (scalarReductionSource l E Y))
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K) (n : ℕ) :
    (T.reductionEvaluation n).inv.app ((integralDerivedPullback l E f).obj K) ≫
      (finiteSystemDerivedEvaluation (integralSystemRings l E)
        (integralSystemTransition l E) X n).map
        (T.reduction.map (M.realization.hom.app K) ≫
          T.adjunction.counit.app
            ((integralComparisonDerivedSequencePullback l E f).obj (S.reduction.obj K))) ≫
      (finiteSystemDerivedPullbackEvaluation (integralSystemRings l E)
        (integralSystemTransition l E) f n).hom.app (S.reduction.obj K) ≫
      (proEtaleConstantRingDerivedPullback
        (Padic.coefficientExtensionRing l E (n + 1)) f).map
        ((S.reductionEvaluation n).hom.app K) =
    integralPullbackFiniteComparison l E f K P e n ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (integralFinitePullbackModel l E f n)
          (ComplexShape.up ℤ)).hom.app
            ((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj)) ≫
      (proEtaleConstantRingPullback
        (Padic.coefficientExtensionRing l E (n + 1)) f).mapDerivedCategoryFactors.inv.app
          ((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj) ≫
      (proEtaleConstantRingDerivedPullback
        (Padic.coefficientExtensionRing l E (n + 1)) f).map
        ((coefficientFiniteReductionModel l E Y P.obj P.property.1 n).inv ≫
          (scalarReductionDerivedExtension l E Y n).map e.hom)
```

## New

The same signature, verbatim, in its recorded module, with the existing named
proof obligation `:= by sorry`. Its docstring gives the source, blueprint id,
and full natural-language proof. No definition, signature, or public instance
is changed. It remains one lower hole, restoring the C4 decomposition.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralPullbackCounitProjection | unclaimed | Restore the existing attached statement. |
| Sheaf.Paper.IntegralPullbackSystemComparison | W5 | Import its finite map equality; construct and prove invertibility separately. |

There are no live Lean importers of the absent module. The existing DAG parent
is lem-pod-integral-pullback-system-comparison; its eight dependencies and unit
route remain intact. All higher consumers keep the identical main interface.

## Status

landed 20261026T071427-L-3928454 2026-10-26 (merge of deliver/W5/Sheaf.Paper.IntegralPullbackSystemComparison)
