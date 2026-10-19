# WeilConjectures.integralOperationsWellDefined

## Reason

The completed proof adds private lemmas, proof sections and local elaboration commands.
The static interface checker records commands such as `open`, `variable`, `section`
and local `attribute` changes even when they export no new mathematical interface.
This record documents that command change and the three new fully proved public
coefficient results. Every original declaration, including all instances and
construction bodies, retains its exact interface and defining module. All ten
public imports are unchanged. There is no definition or statement repair.

Local irreducibility avoids expanding coefficient and product constructions while
elaborating proofs. It is scoped to the proof sections and does not change their
reducibility for importers. Proof-only imports supply the actual declarations
needed by this route; their additions and removals are listed in report.md.

## Old

The original nondeclaration commands, as read by the interface checker, are:

```lean
@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 512
universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option backward.isDefEq.respectTransparency false
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
```

The three independent-coefficient modules did not exist. The main theorem had
its present statement and an unproved proof. Original public definitions and
instances are reproduced unchanged, rather than extracted into a new module.

## New

The new nondeclaration commands, as read by the interface checker, are:

```lean
@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 512
universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option backward.isDefEq.respectTransparency false
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
attribute [local irreducible] constantSheaf limit
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Opposite
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
attribute [local irreducible] constantSheaf limit WeilConjectures.unrestrictedIntegralReductionExistence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
attribute [local irreducible] constantSheaf limit WeilConjectures.unrestrictedIntegralReductionExistence
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] constantSheaf limit
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ZeroObject
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
attribute [local irreducible] constantSheaf limit
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
attribute [local irreducible] constantSheaf limit
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
attribute [local irreducible] constantSheaf limit
set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Opposite
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
attribute [local irreducible] constantSheaf limit
set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
attribute [local irreducible] constantSheaf limit
attribute [local irreducible] integralOperationsPullbackComplexFunctor integralOperationsTensorComplexFunctor integralOperationsPullbackTowerFunctor integralOperationsTensorTowerFunctor integralOperationsDerivedLimitProperty integralOperationsGoodComplex integralOperationsGoodLocalization integralOperationsPullbackOnGood integralOperationsTensorOnGood
```

The added coefficient theorem signatures are recorded verbatim in the lean records
of `lem-pur-change-of-rings-tensor-cancellation-independent`,
`lem-pur-kflat-change-of-rings-independent`, and
`lem-pur-coefficient-pullback-exact`. All three are fully proved. No original
signature or definition changes; comparison of every original interface entry
other than the command list succeeds byte for byte after the checker's parsing.
The final combined compile succeeds, including artifact generation, in 49.5 seconds
for the item module.

## Users

The current-source inventory from `tools/downstream.py --direct --names` lists
27 direct importers, all recorded below with their current holders. Two unchanged
consumers, `IntegralDerivedOperations` and `IntegralTowerLimitComparison`, compiled
against the delivered artifacts in 34.0 and 47.6 seconds respectively. The latter
is now transitive in the current shared-source inventory.

No downstream adaptation is needed: every original declaration and instance has
exactly the same statement, body and module, and the local commands add no exported
attribute. The new modules have no prior consumers in the shared library and are
proof-only dependencies of this item. There are no changed declaration names for
a `tools/downstream.py --uses` inventory: the static change is its synthetic command
list entry, not a declaration. No module held by another group is edited.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.MilnorTower | unclaimed | Unchanged; all imported signatures, definitions and instances preserved. |
| Sheaf.AlgebraicGeometry.ProEtaleMilnorSequence | unclaimed | Unchanged; all imported signatures, definitions and instances preserved. |
| Sheaf.Paper.CanonicalCoefficientPullbackReduction | unclaimed | Unchanged; all imported signatures, definitions and instances preserved. |
| Sheaf.Paper.CompletedOperationTowerSubstitution | T1 | Unchanged; all imported signatures, definitions and instances preserved. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | A4 | Unchanged; all imported signatures, definitions and instances preserved. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | Y9 | Unchanged; all imported signatures, definitions and instances preserved. |
| Sheaf.Paper.DerivedPullbackTensorIso | W3 | Unchanged; all imported signatures, definitions and instances preserved. |
| Sheaf.Paper.DirectImagesConstructible | unclaimed | Unchanged; all imported signatures, definitions and instances preserved. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | X3 | Unchanged; all imported signatures, definitions and instances preserved. |
| Sheaf.Paper.IntegralDerivedOperations | unclaimed | Unchanged; compiled against the final packet. |
| Sheaf.Paper.IntegralLineTensorComparison | unclaimed | Unchanged; all imported signatures, definitions and instances preserved. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | Y8 | Unchanged; all imported signatures, definitions and instances preserved. |
| Sheaf.Paper.IntegralPointTransportTowerRealization | E9 | Unchanged; all imported signatures, definitions and instances preserved. |
| Sheaf.Paper.IntegralPullbackComparisonRealization | A5 | Unchanged; all imported signatures, definitions and instances preserved. |
| Sheaf.Paper.IntegralPullbackCompletedComparison | P4 | Unchanged; all imported signatures, definitions and instances preserved. |
| Sheaf.Paper.IntegralPullbackComposition | A7 | Unchanged; all imported signatures, definitions and instances preserved. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unclaimed | Unchanged; all imported signatures, definitions and instances preserved. |
| Sheaf.Paper.IntegralScalarExtensionWellDefined | P7 | Unchanged; all imported signatures, definitions and instances preserved. |
| Sheaf.Paper.IntegralTensorPullback | J2 | Unchanged; all imported signatures, definitions and instances preserved. |
| Sheaf.Paper.OrdinaryCompletedIntegralPullback | G7 | Unchanged; all imported signatures, definitions and instances preserved. |
| Sheaf.Paper.RationalCoefficientCategoryComparison | T2 | Unchanged; all imported signatures, definitions and instances preserved. |
| Sheaf.Paper.RationalSliceCompletedEvaluation | unclaimed | Unchanged; all imported signatures, definitions and instances preserved. |
| Sheaf.Paper.SpecifiedPullbackComparisonAlpha | Y6 | Unchanged; all imported signatures, definitions and instances preserved. |
| Sheaf.SixFunctors.CompletedTensorShiftRight | unclaimed | Unchanged; all imported signatures, definitions and instances preserved. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | W8 | Unchanged; all imported signatures, definitions and instances preserved. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Unchanged; all imported signatures, definitions and instances preserved. |
| Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization | P7 | Unchanged; all imported signatures, definitions and instances preserved. |
| Sheaf.Paper.IntegralTowerLimitComparison | unclaimed | Unchanged transitive consumer; compiled against the final packet. |

## Status

landed 20261019T192732-L-1861313 2026-10-19 (merge of deliver/G1/Sheaf.Paper.IntegralOperationsWellDefined)
