# WeilConjectures.ProjectionTensorCoefficient.total

## Reason

Restore the quarantined module recorded in coord/rework.tsv. The archived total
constructor fails to synthesize the intended MonoidalCategory when inferring the
module category from fdCoefficientTransport. Explicitly specify its source and
target categories, and bind the same functor with its existing additive instance.
The construction remains tensorPullbackTotal with the same moduleComparison and
the same naturality proof; no summand, differential, completion, or orientation changes.

The two existing backward.isDefEq.respectTransparency options are set to false so
Lean can identify the existing abelian and concrete module preadditive instances.
All nine public declaration signatures and existing docstrings stay verbatim.
The added coefficientIso and tensor_hom_ext are private helpers used only in proofs.

Remove the unused public imports RationalCoefficientCategoryComparison,
WfTensorCompletionFrobenius and OpenFactorTensorModel. Import FdCoefficientComparison
publicly for the actual coefficient functor used in the signatures; retain
ConstructibleTensorCompletion for the existing tensor definitions. The only added
proof import is RingIsomorphismTensorTransport. No source-library file is changed.

## Old

```lean
def total (P Q : CochainComplex (integralTowerModules l E X) ℤ) :
    (totalTarget l E X).obj (P, Q) ⟶
      (complexTransport l E X).obj ((constructibleTensorTotal l E X).obj (P, Q)) :=
  letI : MonoidalCategory (integralTowerModules l E X) :=
    SheafOfModules.monoidalCategory (completedIntegralCommRingSheafUnrestricted l E X)
  letI : MonoidalCategory (pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E))) :=
    SheafOfModules.monoidalCategory (pbcAdicCompletion X (pbcIntegralDatum l E))
  letI : MonoidalPreadditive (integralTowerModules l E X) :=
    proEtaleTensorPreadditive X (completedIntegralCommRingSheafUnrestricted l E X)
  letI : MonoidalPreadditive
      (pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E))) :=
    proEtaleTensorPreadditive X (pbcAdicCompletion X (pbcIntegralDatum l E))
  tensorPullbackTotal (fdCoefficientTransport l E X) (moduleComparison l E X)
    (module_tensorHom_naturality l E X) P Q
```

Original public imports:

```lean
public import Sheaf.Paper.RationalCoefficientCategoryComparison
public import Sheaf.Paper.WfTensorCompletionFrobenius
public import Sheaf.SixFunctors.ConstructibleTensorCompletion
public import Sheaf.SixFunctors.OpenFactorTensorModel
```

## New

```lean
def total (P Q : CochainComplex (integralTowerModules l E X) ℤ) :
    (totalTarget l E X).obj (P, Q) ⟶
      (complexTransport l E X).obj ((constructibleTensorTotal l E X).obj (P, Q)) :=
  letI : MonoidalCategory (integralTowerModules l E X) :=
    SheafOfModules.monoidalCategory (completedIntegralCommRingSheafUnrestricted l E X)
  letI : MonoidalCategory (pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E))) :=
    SheafOfModules.monoidalCategory (pbcAdicCompletion X (pbcIntegralDatum l E))
  letI : MonoidalPreadditive (integralTowerModules l E X) :=
    proEtaleTensorPreadditive X (completedIntegralCommRingSheafUnrestricted l E X)
  letI : MonoidalPreadditive
      (pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E))) :=
    proEtaleTensorPreadditive X (pbcAdicCompletion X (pbcIntegralDatum l E))
  let F : integralTowerModules l E X ⥤
      pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E)) :=
    fdCoefficientTransport l E X
  letI : F.Additive := fdCoefficientTransportAdditive l E X
  tensorPullbackTotal
    (A := integralTowerModules l E X)
    (B := pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E)))
    F (moduleComparison l E X)
    (module_tensorHom_naturality l E X) P Q
```

New public imports:

```lean
public import Sheaf.Paper.FdCoefficientComparison
public import Sheaf.SixFunctors.ConstructibleTensorCompletion
```

## Users

`tools/downstream.py --allow-missing --uses` finds no current live consumers,
because the item is quarantined. An explicit search of both lean/ and quarantine/
finds the following archived direct importer. Its own imports already include all
three removed re-exports, so its statement environment is preserved.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | unclaimed in local claim records; quarantined | Same nine declarations and total-map formula; no adaptation. Consumer compilation recorded in report.md. |

The DAG parents fix-prop-projection-formula and
def-sf-projection-tensor-coefficient-comparison still use this item. Neither their
statements nor the unit route changes. No target statement or definition meaning changes.

## Status

landed 20261021T233800-L-862182 2026-10-21 (merge of deliver/Q3/Sheaf.Paper.ProjectionCoefficientTensorTotal)
