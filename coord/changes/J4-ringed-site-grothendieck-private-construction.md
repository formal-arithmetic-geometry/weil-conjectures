# SheafOfModules.isGrothendieckAbelianOfUniverses

## Reason

The proof uses private free-representable presheaves with independent universes.
The static interface checker notices the additional `open`, `section`, `variable`,
local `set_option` commands and attributes on private computation lemmas. They
support only this proof. The public theorem type and the four public imports
stay identical. No target type or definition changes. The private definitions
are explicit Finsupp constructions with fully proved laws.

## Old

```lean
open CategoryTheory

namespace SheafOfModules
```

The public signature was:

```lean
theorem isGrothendieckAbelianOfUniverses
    {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
    (R : Sheaf J RingCat.{r}) :
    IsGrothendieckAbelian.{max c h r s}
      (ringedSiteModules.{max c h r s} R)
```

## New

```lean
open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

section

variable {C : Type c} [Category.{h} C] (R : Cᵒᵖ ⥤ RingCat.{r})
```

This section contains private `freeObj`, `freeObj_map_single`, `freeDesc`, and
`freeDesc_single`, and ends before the existing public theorem. The private
construction definitions use a local
`set_option backward.isDefEq.respectTransparency false in`; the two private
computation lemmas carry `@[simp]`. These are not public API declarations.

The public signature is still:

```lean
theorem isGrothendieckAbelianOfUniverses
    {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
    (R : Sheaf J RingCat.{r}) :
    IsGrothendieckAbelian.{max c h r s}
      (ringedSiteModules.{max c h r s} R)
```

## Users

`tools/downstream.py` reports the following downstream modules and declaration
users. All keep the same statements, definitions and universes because this is
an implementation of the original theorem with private helpers. No consumer
source needs changing. The public imports are identical, and the new proof
imports are not reexported. Holders are the current local claim records.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ClosedSupportStratumHom | D3 | Same public theorem type and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction | E1 | Same public theorem type and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedPullbackTensorComparison | E2 | Same public theorem type and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum | E3 | Same public theorem type and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalClosedSupportAdjunction | unclaimed | Same public theorem type and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.InjectiveComplexSliceSectionModel | H2 | Same public theorem type and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtale.HypercoverComplex | C8 | Same public theorem type and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtale.SectionsConservative | D5 | Same public theorem type and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleContinuousCohomologyLimit | unclaimed | Same public theorem type and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleFiniteLocallyProjective | unclaimed | Same public theorem type and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleLeftComplete | U9 | Same public theorem type and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleLeftCompleteTruncationTower | F9 | Same public theorem type and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenExtensionProducts | V7 | Same public theorem type and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleProductsDerived | unclaimed | Same public theorem type and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleWContractibleSectionsDerived | K3 | Same public theorem type and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | W8 | Same public theorem type and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHypercoverEtaleDescent | unclaimed | Same public theorem type and imports; no adaptation. |
| Sheaf.CategoryTheory.LeftModuleDerivedEvaluationForget | P1 | Same public theorem type and imports; no adaptation. |
| Sheaf.CategoryTheory.ModuleRestrictionKernelComparison | unclaimed | Same public theorem type and imports; no adaptation. |
| Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses | J4 | Same public theorem type and imports; no adaptation. |
| Sheaf.CategoryTheory.SiteAugmentationSpectralSequence | unclaimed | Same public theorem type and imports; no adaptation. |
| Sheaf.CategoryTheory.Sites.UnboundedSectionsLocalization | A8 | Same public theorem type and imports; no adaptation. |
| Sheaf.Paper.AmbientIndDerivedSums | F5 | Same public theorem type and imports; no adaptation. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | F6 | Same public theorem type and imports; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | T6 | Same public theorem type and imports; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | E1 | Same public theorem type and imports; no adaptation. |
| Sheaf.Paper.CoefficientHeartClosure | unclaimed | Same public theorem type and imports; no adaptation. |
| Sheaf.Paper.CompleteResidueCohomologyBounds | unclaimed | Same public theorem type and imports; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | U7 | Same public theorem type and imports; no adaptation. |
| Sheaf.Paper.ConstructibleCompactnessBounded | R4 | Same public theorem type and imports; no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | C7 | Same public theorem type and imports; no adaptation. |
| Sheaf.Paper.FormalClosedSupportDerived | W5 | Same public theorem type and imports; no adaptation. |
| Sheaf.Paper.IndHeartKernelsCokernels | M3 | Same public theorem type and imports; no adaptation. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed | Same public theorem type and imports; no adaptation. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | H9 | Same public theorem type and imports; no adaptation. |
| Sheaf.Paper.LocalizingClosureExistence | P1 | Same public theorem type and imports; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | Q3 | Same public theorem type and imports; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | K6 | Same public theorem type and imports; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | F8 | Same public theorem type and imports; no adaptation. |
| Sheaf.Paper.SiteHypercoverDerivedDescent | unclaimed | Same public theorem type and imports; no adaptation. |
| Sheaf.Paper.TAdmissibleDualizableTruncations | unclaimed | Same public theorem type and imports; no adaptation. |
| Sheaf.SixFunctors.BrownHypothesesAmbient | Z8 | Same public theorem type and imports; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | M7 | Same public theorem type and imports; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | N4 | Same public theorem type and imports; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | U3 | Same public theorem type and imports; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | G9 | Same public theorem type and imports; no adaptation. |
| Sheaf.SixFunctors.UnboundedClassicalTruncation | Y2 | Same public theorem type and imports; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | U1 | Same public theorem type and imports; no adaptation. |
| Sheaf.TraceFormula.TotalSiteDerivedComponents | unclaimed | Same public theorem type and imports; no adaptation. |

## Status

landed 20261018T145105-L-3641632 2026-10-18 (merge of deliver/J4/Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses)
