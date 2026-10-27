# AlgebraicGeometry.Scheme.RingedRestrictionExchange.degreeZero_normalization

## Reason

The raw concrete equality causes very expensive kernel conversion between the
preadditive/zero and derived-category instances on categories of module sheaves.
The generic calculation and its specialization with the functors still variable
check quickly. Record the same equality by a transparent proposition before
specializing its functors. This is an interface refactor of this Sheaf theorem,
not a correction of its mathematical assertion.

Three unused direct public imports are also removed: the constant-ring operations,
the condensed ambient wrapper, and the arbitrary-resolution derived-functor interface.
Their extra interfaces do not occur in this module's declarations or proofs.
The arbitrary-ring operations and ordinary right-derived APIs remain available.

## Old

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Paper.CondensedAmbientExchange
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
```


```lean
theorem degreeZero_normalization (r : StrictTowerRingedSquare sq)
    (M : proEtaleRingModules X r.RX) :
    (basePull r).mapDerivedCategory.map (degreeZeroComparison (verticalPush r) M) ≫
        (exchange r).app
          (DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj M)) ≫
        (targetPush r).rightDerivedFunctor.map (degreeZeroPullIso (upperPull r) M).hom =
      (degreeZeroPullIso (basePull r) ((verticalPush r).obj M)).hom ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.single _ (.up ℤ) 0).map ((ordinary r).app M)) ≫
        degreeZeroComparison (targetPush r) ((upperPull r).obj M)
```

## New

```lean
public import Sheaf.CategoryTheory.DerivedDegreeZeroExchangeEquation

attribute [local instance 30000]
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
```


```lean
theorem degreeZero_normalization (r : StrictTowerRingedSquare sq)
    (M : proEtaleRingModules X r.RX) :
    DerivedDegreeZeroExchangeEquation (verticalPush r) (basePull r)
      (upperPull r) (targetPush r) (ordinary r) (exchange r)
      (degreeZeroComparison (verticalPush r)) (degreeZeroComparison (targetPush r))
      (degreeZeroPullIso (basePull r)) (degreeZeroPullIso (upperPull r)) M
```

`CategoryTheory.DerivedDegreeZeroExchangeEquation` unfolds to precisely the old
equality. Its four comparison arguments above are the original canonical maps;
there are no extra hypotheses or existentially selected data. The generic private
`degreeZero_of_chain` proves the expanded equality itself. The new definition has
no proof hole. Existing `degreeZeroComparison` and `degreeZeroPullIso` are unchanged.
The file locally prioritizes the native module-sheaf derived-category instance
`proEtaleRingModules_hasDerivedCategory`; the alternative reduction-module
instance also constructs `HasDerivedCategory.standard`. The file locally prioritizes
`SheafOfModules.wEqualsLocallyBijective_coefficientUniverse`, matching the
abelian-category presentation used to construct that native localization. The
alternative `completedConstantAbLocallyBijective` proof otherwise caused an
expensive kernel comparison. This selects a proof of the same local-bijection
property; the category, operations, canonical comparisons and all old definition
bodies and other theorem statement texts are unchanged. The separate open
preservation/API and OpenCube relocation changes are recorded in
`coord/changes/c5-open-kinjective-preservation-api.md`. No priority is exported.
No target signature, source-library declaration or existing definition changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RingedRestrictionExchangeOpenDescent | C5 | The degree-zero theorem uses transparent notation and is proved from exchange_chainUnit. |

`tools/downstream.py` reports zero downstream modules and lists only the item as
using `degreeZero_normalization`. No direct importer exists to adapt or compile.
The four DAG citers were read: native-weil-proper-natural-base-change,
continuous-adic-proper-base-change-restriction,
field-shriek-integral-component-naturality, and
condensed-exchange-one-open-restriction (their full IDs are in the item report).
Their mathematical assertions remain identical: expanding the proposition gives
the same normalization; all other clauses are unchanged. The item's mathematical
node statement is unchanged; its statement dependencies now include the owner of
this notation. There is no target-definition change reopening a target review.

## Status

landed 20261026T222602-L-670542 2026-10-26 (merge of deliver/C5/Sheaf.AlgebraicGeometry.RingedRestrictionExchangeOpenDescent)
