# integralProjectionDirectFactorEvaluation proof context

## Reason

The proof uses local implicit reducibility of the coordinate and category wrappers to recognize the source and target
scheme projections during category-theoretic rewriting. The conservative command scanner
may classify this as an interface change. The attribute is explicitly local, and the
existing theorem signature, attributes and public imports stay unchanged. The finite
normalization calculation requires a larger elaborator heartbeat budget; the compile
still must finish within the unchanged 60-second file limit.

## Old

```lean
theorem integralProjectionDirectFactorEvaluation
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorOperationDatum D C E n hn) (hl : IsUnit (C.l : D.k))
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left) (m : ℕ)
    (M : sfIntegralConstructibleCategory C.l E (identitySquare f c).Z.obj.left) :
    (coefficientSequenceDerivedEvaluation C.l E Y.obj.left m).map
        (ProjectionFactors.directReduction D C E n hn S hl o z f c M) ≫
      ((o.evaluation c.g).evaluation m).hom.app
        ((calculus C.l E c.Z).reduction.obj M.obj) ≫
      (proEtaleConstantDerivedDirectImage c.g
        (Padic.coefficientExtensionRing C.l E (m + 1))).map
          (((calculus C.l E c.Z).reductionEvaluation m).hom.app M.obj) =
    ((calculus C.l E Y.obj.left).reductionEvaluation m).hom.app
        (((S.higher.integralExchange (identitySquare f c)).stage.properPush.obj M).obj) ≫
      (FactorEvaluation.direct D C E n hn S f c m M).hom
```

The original module has no local reducibility command for `identitySquare` and uses the
default elaborator heartbeat budget.

## New

The signature above is unchanged. The proof-only context adds:

```lean
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus

attribute [local implicit_reducible] identitySquare sixFunctorIntegralReduction
  coefficientFiniteDerivedExtension sixFunctorFinitePullback
  Over.Hom Over.homMk CostructuredArrow.homMk
  scalarReductionSourceDerived scalarReductionTargetDerived integralCoefficientSheaf
  integralCoefficientCommRingSheaf integralOperationsCommHasDerivedCategory
  integralCompletedRingHasDerivedCategory integralTowerHasDerivedCategory
  coefficientFiniteHasDerived reductionModulesHasDerivedCategory SemilinearSections.moduleAbelian
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory scalarReductionDerivedExtension

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  SheafOfModules.instAbelian
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000 in
-- Transporting the derived adjunctions elaborates dependent functor comparison squares.
```

The heartbeat option scopes only the theorem command. The two `respectTransparency`
options are true. The additional pullback-evaluation import is private. The four new
helpers are private proved theorems. No global attribute, definition or existing public
interface changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralProjectionDirectFactorEvaluation | W5 | Proof completed; signature unchanged. |
| Sheaf.Paper.IntegralProjectionSupportFactorCoordinates | unclaimed | Sole direct importer; identical statement and public imports, local proof context does not escape. No adaptation. |

The direct importer was found by exact import-line search in `lean/`. No changed shared
interface requires consumer adaptations.

## Status

landed 20261027T094534-L-240471 2026-10-27 (merge of deliver/W5/Sheaf.Paper.IntegralProjectionDirectFactorEvaluation)
