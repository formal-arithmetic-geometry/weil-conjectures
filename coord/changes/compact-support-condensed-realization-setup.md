# CompactSupportCondensedRealization setup export

## Reason

The original monolithic file exceeded the 60-second compile limit even before adding
proofs (74.2 seconds). Profiling, a local derived-category unfolding barrier, local
instance priority experiments and further local composite barriers did not put the
complete proof file under the limit (the best complete run was 67.1 seconds).
Split the self-contained prefix into CompactSupportCondensedRealizationSetup.
All 48 moved public names, signatures, definition bodies and exported attributes stay
identical; two theorem bodies now have proofs. The item publicly imports the setup,
so consumers continue to see all original declarations. No target statement changes.
Six original sorry bodies move with their declarations; none is added or renamed.

The direct-importer checks exposed a pre-existing compile-time failure in the unclaimed
Sheaf.Paper.CompactSupportRealizationFactorNormalization: the unchanged baseline took
70.8 seconds, and the original against this delivery took 81 seconds. Add the same local
derived-category barriers and synchronous elaboration used in the item, plus local
barriers for derived comparison isomorphisms and the point inverse image. Enable
respecting transparency separately for the declarations that compile with it; retain
the original global options for the six declarations that need their original context.
The first repaired file passed standalone compilation in 34.0 seconds, but its delivery
compile took 65 seconds and was rejected. Profiling showed distributed typeclass and
kernel-checking cost. A trial local priority for existing category instances did not
improve it and was removed. After these optimization attempts, separated the self-contained
prefix through systemPresentation into CompactSupportRealizationCoordinates and publicly
re-exported it. Both separated files passed remote compilation. The 32 public declarations, definition
bodies, proofs and exported attributes are unchanged. Three original holes move; none is added. Recombining the source
files and removing only comments and local elaboration commands restores all original
declaration tokens. Existing coordinate-definition ownership and the factor-normalization
node are updated, and a setup node records the original prefix.

Reviewer correction (cc review of a8b2f30fa2db, 2026-10-27): the delivery also added a
private `import all Sheaf.Paper.CondensedCompactSupportProjection` to the unclaimed importers
Sheaf.Paper.CondensedOpenCounitUnits and Sheaf.Paper.CondensedOpenCounitRealization, citing a
kernel error. The unchanged originals of both modules compile against the delivered modules
(40.7 s and 6.1 s, lcompile against the published build), so that adaptation is not forced
and was withdrawn: both modules stay byte-identical to the published version.

## Old

The importer's original local context began:

```lean
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Mod.monoidalCategory
  CategoryTheory.Sheaf.monoidalCategory
```

The prefix through systemPresentation was declared in
lean/Sheaf/Paper/CompactSupportRealizationFactorNormalization.lean. Its first public import was:

```lean
public import Sheaf.Paper.FiniteFieldFiber
```

Its complete declaration source is unchanged.



The prefix through latticeScalar is declared in
lean/Sheaf/Paper/CompactSupportCondensedRealization.lean. Its public imports are:

```lean
public import Sheaf.Paper.CondensedCompactSupportProjection
public import Sheaf.Paper.SemilinearCompactSupportCoefficientTransport
public import Sheaf.Paper.CompactSupportReductionTower
public import Sheaf.SixFunctors.SemilinearProperOpenMatePasting
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.CondensedERealization
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import Sheaf.Paper.CondensedCoefficientComparisons
public import Sheaf.Paper.CompletedCoefficientPresentationTransport
public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison
public import Sheaf.Paper.BasicOperationsCoefficientReduction
```

## New

The importer adds this local context:

```lean
set_option Elab.async false
attribute [local irreducible] HasDerivedCategory.ofHasKInjectiveResolutions
  _root_.instCategoryDerivedCategory
  CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctorIsoMapDerivedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
```

Immediately before each declaration except restrictionSquare, realizationPull,
coefficient_factorization, coefficient_proper_transpose, structural_conjugacy and
ordinaryPushIdentity_existsUnique, it enables:

```lean
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
```

The original global options are preserved. No option disabling transparency is added.

The importer now re-exports the separated coordinate module immediately after that import:

```lean
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.CompactSupportRealizationCoordinates
```

Every original public import is retained. The 32 original coordinate declarations now
live in the new module; all remaining declarations stay in the importer. Its three moved
unfinished theorems are attached to lem-zl-compact-support-realization-coordinates-setup;
the original definition-ownership node changes only its Lean attachment.



The same prefix is declared in
lean/Sheaf/Paper/CompactSupportCondensedRealizationSetup.lean. The item's public imports are:

```lean
public import Sheaf.Paper.CondensedCompactSupportProjection
public import Sheaf.Paper.CompactSupportCondensedRealizationSetup
public import Sheaf.Paper.SemilinearCompactSupportCoefficientTransport
public import Sheaf.Paper.CompactSupportReductionTower
public import Sheaf.SixFunctors.SemilinearProperOpenMatePasting
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.CondensedERealization
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import Sheaf.Paper.CondensedCoefficientComparisons
public import Sheaf.Paper.CompletedCoefficientPresentationTransport
public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison
public import Sheaf.Paper.BasicOperationsCoefficientReduction
```

The setup node records the moved declarations; its main declaration is the unchanged
IntegralModel structure. The six existing unfinished theorems retain their original
statements and complete docstring proof plans. No assumption of an IntegralModel or a
ComparisonFamily is manufactured by moving the definitions.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CompactSupportCondensedRealization | J1 | Re-exports its unchanged setup declarations; compile checked. |
| Sheaf.Paper.PurIntegralSupportComparison | unclaimed | Same public declarations through the setup re-export; compile checked. |
| Sheaf.Paper.CondensedOpenCounitRealization | unclaimed | Unchanged; same public declarations through the setup re-export; compile checked. |
| Sheaf.Paper.CompactSupportRealizationFactorization | unclaimed | Same public declarations through the setup re-export; compile checked. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Same public declarations through the setup re-export; compile checked. |
| Sheaf.Paper.CondensedOpenCounitComparisons | unclaimed | Same public declarations through the setup re-export; compile checked. |
| Sheaf.Paper.MixedCupRingedNormalization | unclaimed | Same public declarations through the setup re-export; compile checked. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | unclaimed | Same public declarations through the setup re-export; compile checked. |
| Sheaf.Paper.PurIntegralSupportComparisonData | unclaimed | Same public declarations through the setup re-export; compile checked. |
| Sheaf.Paper.CondensedExceptionalReconstructionData | unclaimed | Same public declarations through the setup re-export; compile checked. |
| Sheaf.Paper.ExceptionalReconstructionContext | unclaimed | Same public declarations through the setup re-export; compile checked. |
| Sheaf.Paper.CondensedOpenCounitUnits | unclaimed | Unchanged; same public declarations through the setup re-export; compile checked. |
| Sheaf.Paper.FilteredCondensedRepresentingPairData | unclaimed | Same public declarations through the setup re-export; compile checked. |
| Sheaf.Paper.ExceptionalReconstructionComparison | unclaimed | Same public declarations through the setup re-export; compile checked. |
| Sheaf.Paper.PurIntegralRepresentingPair | unclaimed | Same public declarations through the setup re-export; compile checked. |
| Sheaf.Paper.CompactSupportRealizationFactorNormalization | unclaimed | Local elaboration repair and coordinate separation for its existing timeout; same declarations and proofs. |
| Sheaf.Paper.ExceptionalRealizationNormalization | unclaimed | Same public declarations through the setup re-export; compile checked. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | unclaimed | Same public declarations through the setup re-export; compile checked. |

All 17 current direct importers of the item passed the first compatibility checks.
All five direct importers of CompactSupportRealizationFactorNormalization passed again
after the coordinate separation. Unchanged
consumer copies and diagnostic sources were removed before delivery.

## Status

landed 20261027T021332-L-2758276 2026-10-27 (merge of deliver/J1/Sheaf.Paper.CompactSupportCondensedRealization)
