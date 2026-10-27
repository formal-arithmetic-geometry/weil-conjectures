# Completion coherence imports and local proof commands

## Reason

Use the existing scalar associator and unit without an import cycle, and keep the large quotient and tensor constructions abstract during categorical proofs. The three extracted declarations retain their names, signatures, fields and bodies and are publicly reexported. Functor composition in private helper signatures is parenthesized to match the concrete counits; the mathematical equations are identical. The added local options and attributes affect elaboration only. Profiling found repeated unfolding at the concrete sheaf specializations; keep the K-flat predicate locally irreducible, and supply concrete category parameters explicitly. (The delivery also made `quotientRoos` an abbreviation; the reviewer withdrew that change because it broke importers that set `attribute [local irreducible] quotientRoos`. `quotientRoos` stays the published `noncomputable def`; the item compiles against it.) The product augmentation helper accepts the existing product map and its projection equations, avoiding separate chosen-limit elaborations. The main assembly respects local irreducibility; the concrete unit helper disables backward definitional matching and supplies the descent categories explicitly; typed local counits, explicit localization universes and direct product-projection proofs avoid unresolved functor and universe metavariables in the representative predicate.

## Old

```lean
public import Sheaf.Algebra.Homology.FiniteFreeCompletionExchange
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Sheaf.CategoryTheory.StrictRoosComparison
public import Sheaf.CategoryTheory.CompactSupportRoosCofinality
public import Sheaf.CategoryTheory.StrictRoosAdditiveComparison
import Sheaf.Algebra.Homology.IdentityQuotientRoosNormalization
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] quotientTower roosF SheafOfModules.monoidalCategory
attribute [local irreducible] scalarTensorSection arithmeticRoosMap
attribute [local irreducible] roosχ quotientMap quotientProduct
attribute [local irreducible] identityPresheafIso identitySheafIso
attribute [local irreducible] identityOrdinaryIso
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
```

## New

```lean
public import Sheaf.Algebra.Homology.PrincipalQuotientCompletionModel
public import Sheaf.Algebra.Homology.FiniteFreeCompletionExchange
public import Sheaf.Algebra.Homology.CompletionRepresentativeAccessors
public import Sheaf.Algebra.Homology.ScalarTensorSection
public import Sheaf.Algebra.Homology.ArithmeticRoosMap
public import Sheaf.Algebra.Homology.RoosRepresentativeComposition
import Sheaf.Algebra.Homology.FiniteFreeQuotientRoosComparison
import Sheaf.Algebra.Homology.FiniteFreeQuotientRoosHorizontalCoherence
import Sheaf.Algebra.Homology.RingedKFlatWordComparisonDescent
import Sheaf.Algebra.Homology.IdentityQuotientRoosNormalization
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] quotientTower roosF SheafOfModules.monoidalCategory
attribute [local irreducible] scalarTensorSection arithmeticRoosMap
attribute [local irreducible] quotientMap quotientProduct roosχ
attribute [local irreducible] CochainComplex.IsKFlatIndependentCoefficients
attribute [local irreducible] RepresentativeComparison
set_option backward.defeqAttrib.useBackward false in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
attribute [local irreducible] roosχ quotientMap quotientProduct
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.FiniteFreeCompletionExchangeCoherence | B4 | Proof assembly and extracted APIs. |
| Sheaf.Algebra.Homology.RingedKFlatWordComparisonDescent | unclaimed | Public import now supplies scalarTensorSection directly; all public signatures are unchanged; two private proofs control scalar-section unfolding explicitly. |
| Sheaf.Algebra.Homology.SectionsScalarDerivedTransport | unclaimed | All original names remain publicly visible. |

These are all direct importers of the item in the current source. The six direct importers of RingedKFlatWordComparisonDescent are ExplicitScalarConeWordCoordinates, FiniteDerivedComparisonNormalization, MixedReductionUnitComposition, SpaceAffinePullPushExchange, SpaceDerivedEtaleChartCalculus and CondensedProfiniteScalarCompatibility; none uses BalancedScalarAssociator or BalancedScalarUnit through the removed import. No target signature or mathematical definition changes. The declaration extractions have separate change records.

## Status

landed 20261025T201357-L-2465468 2026-10-25 (merge of deliver/B4/Sheaf.Algebra.Homology.FiniteFreeCompletionExchangeCoherence)
