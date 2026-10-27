# integralProjectionSupportFactorCoordinates

## Reason

Record the proof-local command changes conservatively flagged by stage-3 preflight.
The existing declaration signature, attributes and public imports are unchanged.
The proof adds an `open AlgebraicGeometry.Scheme` command and local reducibility
attributes to keep the concrete category expressions well typed during rewriting.
The attributes are explicitly `[local ...]`, scoped to this module. They do not
change unfolding for importers. All new helpers in the item module are private and
proved. New public coordinate definitions belong to the four new Sheaf modules
and are recorded in their four new nodes.

## Old

The original theorem signature is:

```lean
theorem integralProjectionSupportFactorCoordinates
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorOperationDatum D C E n hn) (hl : IsUnit (C.l : D.k))
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
    let A := S.higher.integralExchange (identitySquare f c)
    let r := ProjectionFactors.supportMap A K
    ProjectionFactors.directReduction D C E n hn S hl o z f c
        (A.stage.openExtension.obj K) ≫
      (Operations.push C.l E o c.g).map
        (ProjectionFactors.openReduction D C E n hn S hl o z f c K) =
      (calculus C.l E Y.obj.left).reduction.map r.hom ≫
        Coordinates.supportReduction D C E S.higher hl o z f c K
```

The original local irreducibility list ends with `pullbackTensorCalculus`.
There is no local `implicit_reducible` block, and the original `open` command does
not explicitly open `AlgebraicGeometry.Scheme`.

## New

The theorem signature above is kept verbatim. The new proof-only commands are:

```lean
open AlgebraicGeometry.Scheme

attribute [local irreducible] scalarReductionDerivedExtension
  scalarReductionDerivedRestriction

attribute [local implicit_reducible] identitySquare sixFunctorIntegralReduction
  coefficientFiniteDerivedExtension sixFunctorFiniteSupport sfIntrinsicCompactSupport
  Over.homMk CostructuredArrow.homMk scalarReductionSourceDerived
  scalarReductionTargetDerived integralCoefficientSheaf integralCoefficientCommRingSheaf
  integralOperationsCommHasDerivedCategory integralCompletedRingHasDerivedCategory
  integralTowerHasDerivedCategory coefficientFiniteHasDerived reductionModulesHasDerivedCategory
  SemilinearSections.moduleAbelian sixFunctorFactorCompactification
  SixFunctorCompactifiedSquare.compactification
```

No global attribute, instance, notation, definition, statement or public import of
an existing module changes. The original hole is decomposed into the three named
proper, open and finite-coordinate statements listed in the report.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralProjectionSupportFactorCoordinates | X9 | Private proof implementation changes; signature unchanged. |
| Sheaf.Paper.IntegralProjectionOpenFactorReduction | unclaimed | Sole direct importer; original signature and public imports preserved, local attributes do not escape. No adaptation. |

The direct importer was found with the exact import-line search in `lean/`.
There is no existing-interface change requiring consumer adaptations.

## Status

landed 20261027T050655-L-253002 2026-10-27 (merge of deliver/X9/Sheaf.Paper.IntegralProjectionSupportFactorCoordinates)
