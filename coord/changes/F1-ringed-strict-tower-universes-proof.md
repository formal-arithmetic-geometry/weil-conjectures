# CategoryTheory.ringedStrictTowerHomotopyLimitOfUniverses

## Reason

Close the remaining maximum-universe companion theorem using the complete private
construction already proved in RingedStrictTowerHomotopyLimitIndependentCoefficients.
That companion public-imports the present module, so importing its theorem here
would create a cycle. Reusing its private construction avoids changing any other
module or public interface. The copied transparency override is omitted: the proof
compiles with the default transparency setting. No target definition changes.

## Old

The public theorem signature and public import are unchanged. The previous local
context, verbatim:

```lean
@[expose] public section
set_option autoImplicit false
universe w uC vC r
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace CategoryTheory
```

## New

The previous context remains. Fully proved private helpers are enclosed in:

```lean
namespace UniverseProof
universe u v u' v' w'
open scoped BigOperators
namespace CoreWork
universe g
variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
variable [HasDerivedCategory.{w} A] [HasCountableProducts (DerivedCategory.{w} A)]
variable [IsGrothendieckAbelian.{g} (ℕᵒᵖ ⥤ A)]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
end CoreWork
end UniverseProof
open UniverseProof
```

The `omit` commands affect only individual private lemmas; all helper declarations
are private. The namespaces close before the original theorem. There are no new
public instances, attributes, definitions, declarations, or imports. Added ordinary
imports provide only proof dependencies. The public theorem's full signature,
including universe binders, is retained verbatim. No consumer needs adaptation or
changes its elaborated type, so no consumer copies are delivered.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients | not queried (no adaptation) | Public interface preserved; no change. |
| Sheaf.CategoryTheory.StrictRoosComparison | not queried (no adaptation) | Public interface preserved; no change. |
| Sheaf.CategoryTheory.StrictRoosDerivedLimitComparison | not queried (no adaptation) | Public interface preserved; no change. |
| Sheaf.CategoryTheory.StrictTowerArithmeticRestrictionDefs | not queried (no adaptation) | Public interface preserved; no change. |
| Sheaf.Paper.CoefDerivedSystemEvaluationCalculus | not queried (no adaptation) | Public interface preserved; no change. |
| Sheaf.Paper.CoefTowerCoaugmentation | not queried (no adaptation) | Public interface preserved; no change. |
| Sheaf.Paper.CoefficientRingedSequenceSite | not queried (no adaptation) | Public interface preserved; no change. |
| Sheaf.Paper.CompactSupportReductionTowerConstruction | not queried (no adaptation) | Public interface preserved; no change. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | not queried (no adaptation) | Public interface preserved; no change. |
| Sheaf.Paper.ConstantTowerDirectImageNormalization | not queried (no adaptation) | Public interface preserved; no change. |
| Sheaf.Paper.ExactProductFunctorStrictLimit | not queried (no adaptation) | Public interface preserved; no change. |
| Sheaf.Paper.RingedStrictTowerProjectionMorphism | not queried (no adaptation) | Public interface preserved; no change. |
| Sheaf.Paper.SfCbcExtensionZeroCompletion | not queried (no adaptation) | Public interface preserved; no change. |
| Sheaf.SixFunctors.ConstructibleTensorCompletion | not queried (no adaptation) | Public interface preserved; no change. |
| Sheaf.SixFunctors.IntegralDualizing | not queried (no adaptation) | Public interface preserved; no change. |
| Sheaf.SixFunctors.IntegralDualizingRoosModel | not queried (no adaptation) | Public interface preserved; no change. |
| Sheaf.Targets.SliceRestrictionStrictDerivedLimit | not queried (no adaptation) | Public interface preserved; no change. |

## Status

landed 20261026T222637-L-677284 2026-10-26 (merge of deliver/F1/Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses)
