# Sheaf.Paper.CompletionTriangleComparison proof context

## Reason

The completed proof needs generic private scalar-cone, tensor, Roos, tower, shift
and localization helpers. The module-command checker requires a record for the
additional section variables, namespace-local opens and elaboration options even
when all new declarations are private. This record documents those commands.

All three existing public declarations retain their signatures verbatim. The
bodies of `CompletionTriangle.tower` and `CompletionTriangle.complexCompletion`
are also verbatim; only the theorem's former `sorry` proof is replaced. The five
existing public imports remain verbatim and in the same order. Thus no target
statement or public definition changes meaning, and this proof-context record
does not reopen target statement review. No source-library module is changed.

The colimit instance is explicitly marked `private local instance` and confined
to `ScalarCone`, before the existing public definitions.
No new public declaration, exported instance, notation or attribute is added.

## Old

The original elaboration options and namespace context were:

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite Pretriangulated

namespace AlgebraicGeometry.ProEtale.CompletionTriangle

open AlgebraicGeometry.ProEtale.AdicCompletion
open AlgebraicGeometry.ProEtale.PrincipalReduction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
```

There were no `ScalarCone`, `CoefficientCone`, `RoosCompletion`, `TowerAssembly`,
`EvalCone` or `TowerCalculus` helper blocks. The public theorem had one `sorry`.

## New

The existing options remain, with these additional elaboration controls:

```lean
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
```

The latter is set to `true` before the existing public namespace, set to `false`
inside `TowerCalculus`, and locally set to `false` for selected private proofs.
These options govern checking this module and do not propagate through imports.
No diagnostic options or increased heartbeat limits remain.

The top-level open is now:

```lean
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory CochainComplex Pretriangulated
```

Private tensor helpers use the following generic context:

```lean
universe vT
namespace ScalarCone
variable {A : Type u} [Category.{vT} A] [Abelian A] [IsGrothendieckAbelian.{vT} A]
  [HasDerivedCategory.{vT} A] [MonoidalCategory A] [MonoidalClosed A]
  [MonoidalPreadditive A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
  {R : Type*} [CommRing R] [Linear R A] [MonoidalLinear R A]
private local instance : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink A
```

Its `include`/`omit` commands select the hypotheses of private helpers only.
`CoefficientCone` opens the pro-etale completion and Nakayama namespaces for its
private coefficient calculations. `RoosCompletion` opens the existing Roos and
completion namespaces and has generic abelian-category and countable-product
variables for its private tensor-tower and sign constructions. These namespaces
end before the original public definitions.

Inside the existing public namespace, `TowerAssembly` and `EvalCone` introduce
generic abelian-category universe variables and local opens; `TowerCalculus`
introduces generic abelian-category variables for the private evaluation,
coherent-shift, cone-triangle and augmentation proofs. The one `open scoped
CategoryTheory.Obj in` command scopes notation to the private countable-exactness
lemma. Every added helper declaration is private and proved, or is a concrete
private definition. All public declarations still use exactly their original
statements and public definitions.

Private proof imports and the node proof dependencies follow the new proof route
listed in the delivery report. Existing importers continue to see the same public
API. The full proof compiled through `lcompile.py` in 58.9 seconds with no warnings;
the corrected private-instance version also passed the delivery compile check.

## Users

The table includes the item and every transitive downstream module returned by
`tools/downstream.py Sheaf.Paper.CompletionTriangleComparison --uses
completion_triangle_comparison tower complexCompletion`. Holders were read from
the coordination claim records when preparing this record. No consumer is edited.

The only external use of `completion_triangle_comparison` is in
`Sheaf.Paper.DerivedNakayamaFirstReduction`, with the same arguments `l E X`.
The textual `tower` matches in `CompactifiedTowerComparisons`,
`IntegralTensorPullback`, `OpenFactorCoherence` and `OpenFactorPullModel` refer to
their own towers or record fields, not a changed declaration of this item.
There are no external textual uses of `complexCompletion`. More generally, for
every row below the same public signatures and concrete definitions ensure that
consumer statements are neither weakened nor strengthened and no adaptation is
needed. In particular, no change to the K6-held module is proposed.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.DeligneLaumon.RawHeartAdicLisseStratification` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.FiniteMapPurity` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.A1FiniteEtaleWeilFibreComparison` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.AdicHomTensorLisseCriterion` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.AdicLisseCohomologyCalculus` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.BrownHypothesesGeneration` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.ClassicalWeilFiltrationHeartTransport` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.CompactSupportLerayFiltration` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.CompactificationCompletedRealization` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.CompactifiedTowerComparisons` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.CompletionTriangleComparison` | F7 | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.CoprojectionCompositionMate` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.DerivedNakayama` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.DerivedNakayamaFirstReduction` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.FieldShriekCompositionQcqs` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.FiniteEtaleAdicCohomology` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.FiniteProductCompactification` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.FourierArtinSchreierProperties` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.IntegralConstantModelHeart` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.IntegralConstructibleExt` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.IntegralConstructibleHeart` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.IntegralProperBaseChange` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.IntegralProperConstructibleHeartBound` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.IntegralResidueClassTriangleClosure` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.IntegralStratumExtBound` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.IntegralStratumHomFormula` | K6 | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.IntegralTensorProduct` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.IntegralTensorPullback` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.LisseCohomologyDerivedDual` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.LisseFieldNormalization` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.LissePointNormalization` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.LissePullbackNormalization` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.LisseRationalRealization` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.LisseRationalRealizationData` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.LisseTensorNormalization` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.NormalizedClassicalWeilRealization` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.PfRefinementCompatibility` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.ProperBaseChangeRational` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.ProperHeartBound` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.ProperHeartConstructibleCohomology` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.ProperOpenBoundaryZero` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.QcqsIntegralFiniteModelCompleteness` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.QcqsProperConstructibleClosedBaseChange` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.RationalRealizationTensorComparison` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.ResidueLisseProjectiveModels` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.SystemClopenTensorCompatibility` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.SystemCompactificationProjectionSubstitution` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.TateTwistLisseLine` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.WfTensorCompletionFrobenius` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.ZlFrobeniusCompactSupportComparison` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.SixFunctors.AmbientProperOpenPasting` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.SixFunctors.CompositionProjectionMate` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.SixFunctors.ConstructibleTensorCompletion` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.SixFunctors.GeneratorReductionStatement` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.SixFunctors.IntegralBasicOperationShift` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeWords` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationComparisonBridge` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationSystemRealization` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.SixFunctors.IntegralRealizationRecursion` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.SixFunctors.IntegralRealizationShiftCoherence` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.SixFunctors.IntegralSystemCanonicalBridge` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.SixFunctors.IntegralTensorInverseImage` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.SixFunctors.OpenAdjunctionShift` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.SixFunctors.OpenExchangeRoosRestriction` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.SixFunctors.OpenFactorCoherence` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.SixFunctors.OpenFactorPullModel` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.SixFunctors.OpenFactorTensorModel` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.SixFunctors.OpenProjectionRoosCompletion` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.SixFunctors.OpenTensorQuotientAugmentation` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.SixFunctors.ProperOpenProjectionMate` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.SixFunctors.SynchronizedCanonicalMaps` | unclaimed | Same public statements, definitions and imports; no adaptation. |
| `Sheaf.SixFunctors.SystemPrimitiveComparisonShift` | unclaimed | Same public statements, definitions and imports; no adaptation. |

## Status

landed 20261021T233700-L-849332 2026-10-21 (merge of deliver/F7/Sheaf.Paper.CompletionTriangleComparison)
