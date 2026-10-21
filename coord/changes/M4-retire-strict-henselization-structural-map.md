# AlgebraicGeometry.Scheme.strictHenselizationStructuralMap_eq

## Reason

Retire the redundant Sheaf wrapper in favor of its proved upstream owners.
The wrapper's small-cone leg equation is already exactly
`(exists_strictHenselizationStructuralMap s).choose_spec j`.
Consumers use that expression directly; the distinct upstream affine-cone equation
with the same short name remains unchanged. No source-library declaration is removed.

## Old

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap

/-!
# The structural morphism of the strict henselization

The strict henselization `S_(s)` of a scheme `S` at a geometric point `s` maps to `S` through
every affine pointed étale neighbourhood; this module names that canonical morphism.

Source: Stacks Project, Tag 03Q9, proof
(blueprint: def-weil-pbc-strict-henselization-structural-map).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The representative limit legs factor through upstream's structure morphism. -/
theorem strictHenselizationStructuralMap_eq
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (j : SmallModel.{u} (strictHenselizationNeighbourhoods s)) :
    (strictHenselizationCone s).π.app (Opposite.op (Opposite.op j)) ≫
        Spec.map (ΓSpecIso
          (((equivSmallModel.{u}
            (strictHenselizationNeighbourhoods s)).inverse.obj j).1.left.unop)).inv ≫
        ((AffineEtale.Spec S).obj
          (((equivSmallModel.{u}
            (strictHenselizationNeighbourhoods s)).inverse.obj j).1)).hom =
      strictHenselizationStructuralMap s := by
  exact (exists_strictHenselizationStructuralMap s).choose_spec j

end AlgebraicGeometry.Scheme
```

## New

The wrapper is withdrawn through deleted.txt and lands as an empty module.
Each current direct consumer replaces the wrapper import, preserving visibility, by:

```lean
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
```

Proofs use the upstream existence theorem's choose_spec in place of the wrapper
leg equation. Backward rewrites first give that equality an explicit structural-map
right side. Every existing signature, definition's data and unrelated proof is retained.
ClosedLift needs a public StructuralMap import for its existing public signature;
the compiler rejects that name when imported only privately.
No target meaning, DAG mathematical dependency or unit route changes.
The private-only AffineLineProjectionStalkBound consumer adds
`set_option linter.privateModule false` after autoImplicit at lines 34–35: the
compiler emits the privateModule warning at line 1 otherwise. Its existing private
helpers stay private. AffineLineInfinityStrictLocalModel keeps its existing setting.

This repair rebases the returned 19d77ccdb packet against current shared sources.
Independently withdrawn modules remain withdrawn, quarantined files remain archived,
and current consumer proofs and API migrations are preserved.
In particular, the stale adaptation of the module held by M1,
`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegular`,
is removed. Its current upstream imports and full colimit-comparison proof stay
verbatim. Its last equation uses the upstream affine cone, not the removed wrapper.
There are no changed lines in that M1 module in this delivery.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResidueLift` | unclaimed | Current independently withdrawn empty module retained; stale restoration removed. No changed lines. |
| `Sheaf.AlgebraicGeometry.EtaleModuleStalkSpecialization` | unclaimed | Replace the wrapper import with the same two upstream public imports. Replace each small-cone leg-equation call by choose_spec. |
| `Sheaf.AlgebraicGeometry.EtaleSectionGermSpecialization` | unclaimed | Replace the wrapper leg equation by the existence theorem’s choose_spec. Replace each small-cone leg-equation call by choose_spec. |
| `Sheaf.AlgebraicGeometry.GeometricSpecializationStrictLocalLift` | unclaimed | Replace the wrapper import with the same two upstream public imports. |
| `Sheaf.AlgebraicGeometry.GmStrictHenselizationPullback` | unclaimed | Replace the wrapper import with the same two upstream public imports. |
| `Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance` | unclaimed | Replace the wrapper import with the same two upstream public imports. |
| `Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalLiftAux` | unclaimed | Replace the wrapper import with the same two upstream public imports. Replace each small-cone leg-equation call by choose_spec. |
| `Sheaf.AlgebraicGeometry.LocalAcyclicityAbelianSheaf` | unclaimed | Replace the wrapper leg equation by the existence theorem’s choose_spec. Replace each small-cone leg-equation call by choose_spec. |
| `Sheaf.AlgebraicGeometry.ModuleSpecializationAbelianIso` | unclaimed | Current source retained verbatim; no adaptation in this packet. Prior sandbox copy removed on rebase, preserving independent withdrawals, quarantines and API repairs. |
| `Sheaf.AlgebraicGeometry.Morphisms.PuncturedRootSectionEtaleDescent` | unclaimed | Current source retained verbatim; no adaptation in this packet. Prior sandbox copy removed on rebase, preserving independent withdrawals, quarantines and API repairs. |
| `Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictHenselRootSection` | unclaimed | Current upstream imports and proofs retained verbatim. Stale adaptation removed on rebase; no changed lines. |
| `Sheaf.AlgebraicGeometry.Morphisms.StrictHenselDivisorQuotientPresentation` | unclaimed | Current source retained verbatim; no adaptation in this packet. Prior sandbox copy removed on rebase, preserving independent withdrawals, quarantines and API repairs. |
| `Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotient` | unclaimed | Current upstream regularity proof and imports retained verbatim; stale sandbox adaptation removed. No changed lines. |
| `Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientDomainPart` | unclaimed | Current source retained verbatim; no adaptation in this packet. Prior sandbox copy removed on rebase, preserving independent withdrawals, quarantines and API repairs. |
| `Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientNoetherian` | R4 | Current R4 proof and imports retained verbatim; already uses upstream StructuralMap and choose_spec. Stale sandbox adaptation removed; no changed lines. |
| `Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegular` | unclaimed | Current M1 proof retained verbatim; its upstream affine-cone equation is distinct. Stale adaptation removed on rebase; no edit required. |
| `Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularAux` | unclaimed | Current source retained verbatim; no adaptation in this packet. Prior sandbox copy removed on rebase, preserving independent withdrawals, quarantines and API repairs. |
| `Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularPart` | unclaimed | Current source retained verbatim; no adaptation in this packet. Prior sandbox copy removed on rebase, preserving independent withdrawals, quarantines and API repairs. |
| `Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootFiniteEtaleModel` | unclaimed | Current upstream imports and proofs retained verbatim. Stale adaptation removed on rebase; no changed lines. |
| `Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationFinite` | M2 (returned head; current source unchanged) | Current upstream imports and proofs retained verbatim. Stale adaptation removed on rebase; no changed lines. |
| `Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationGenericEtale` | G8 (returned head; current source unchanged) | Current upstream imports and proofs retained verbatim. Stale adaptation removed on rebase; no changed lines. |
| `Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootPurityData` | unclaimed | Current upstream imports and proofs retained verbatim. Stale adaptation removed on rebase; no changed lines. |
| `Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootTameNormalization` | unclaimed | Current upstream imports and proofs retained verbatim. Stale adaptation removed on rebase; no changed lines. |
| `Sheaf.AlgebraicGeometry.ProEtaleClassicalStalk` | unclaimed | Replace the wrapper import with the same two upstream public imports. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineAbelianOriginalStalkTotalExchange` | unclaimed | Current source retained verbatim; no adaptation in this packet. Prior sandbox copy removed on rebase, preserving independent withdrawals, quarantines and API repairs. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineOriginalStalkTotalCohomologyExchange` | unclaimed | Current source retained verbatim; no adaptation in this packet. Prior sandbox copy removed on rebase, preserving independent withdrawals, quarantines and API repairs. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalStalkExchangeComparison` | unclaimed | Current source retained verbatim; no adaptation in this packet. Prior sandbox copy removed on rebase, preserving independent withdrawals, quarantines and API repairs. |
| `Sheaf.AlgebraicGeometry.QcqsGeometricExchangeFactorization` | unclaimed | Replace the wrapper import with the same two upstream public imports. |
| `Sheaf.AlgebraicGeometry.Sites.AffineLineInfinityStrictLocalModel` | unclaimed | Replace the wrapper import with the same two upstream public imports. |
| `Sheaf.AlgebraicGeometry.Sites.AffineLineProjectionStalkBound` | unclaimed | Replace the wrapper import with the same two upstream public imports. |
| `Sheaf.AlgebraicGeometry.Sites.FieldHigherDirectImageStalk` | unclaimed | Current source retained verbatim; no adaptation in this packet. Prior sandbox copy removed on rebase, preserving independent withdrawals, quarantines and API repairs. |
| `Sheaf.AlgebraicGeometry.Sites.PolynomialGenericStrictLocalizationField` | unclaimed | Replace the wrapper import with the same two upstream public imports. |
| `Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModel` | unclaimed | Replace the wrapper import with the same two upstream public imports. |
| `Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModelCoeff` | unclaimed | Replace the wrapper import with the same two upstream public imports. |
| `Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModelCoeffData` | unclaimed | Replace the wrapper import with the same two upstream public imports. |
| `Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModelCoeffFractionTrdeg` | unclaimed | Replace the wrapper import with the same two upstream public imports. |
| `Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModelCore` | unclaimed | Replace the wrapper import with the same two upstream public imports. Replace each small-cone leg-equation call by choose_spec. |
| `Sheaf.AlgebraicGeometry.SpecializationCospecializationArrows` | unclaimed | Current source retained verbatim; no adaptation in this packet. Prior sandbox copy removed on rebase, preserving independent withdrawals, quarantines and API repairs. |
| `Sheaf.AlgebraicGeometry.StrictBaseClosedPointLocalizations` | unclaimed | Replace the wrapper leg equation by the existence theorem’s choose_spec. Replace each small-cone leg-equation call by choose_spec. |
| `Sheaf.AlgebraicGeometry.StrictHenselizationAbelianStalkExchangeLocalization` | unclaimed | Current source retained verbatim; no adaptation in this packet. Prior sandbox copy removed on rebase, preserving independent withdrawals, quarantines and API repairs. |
| `Sheaf.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale` | unclaimed | Independently withdrawn empty module retained; stale sandbox restoration removed. No changed lines. |
| `Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiber` | unclaimed | Current source retained verbatim; no adaptation in this packet. Prior sandbox copy removed on rebase, preserving independent withdrawals, quarantines and API repairs. |
| `Sheaf.AlgebraicGeometry.StrictHenselizationClosedImmersionCartesian` | unclaimed | Replace the wrapper import with the same two upstream public imports. |
| `Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift` | unclaimed | Replace the wrapper import and leg equation; make the upstream StructuralMap import public because the existing public theorem signature uses its map. Extension stays private. |
| `Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeSourceStalkIso` | unclaimed | Current source retained verbatim; no adaptation in this packet. Prior sandbox copy removed on rebase, preserving independent withdrawals, quarantines and API repairs. |
| `Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeStalkIsos` | unclaimed | Current source retained verbatim; no adaptation in this packet. Prior sandbox copy removed on rebase, preserving independent withdrawals, quarantines and API repairs. |
| `Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeStalkIsosSource` | unclaimed | Current source retained verbatim; no adaptation in this packet. Prior sandbox copy removed on rebase, preserving independent withdrawals, quarantines and API repairs. |
| `Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeTargetStalkIso` | unclaimed | Current source retained verbatim; no adaptation in this packet. Prior sandbox copy removed on rebase, preserving independent withdrawals, quarantines and API repairs. |
| `Sheaf.AlgebraicGeometry.StrictHenselizationLocalPresentation` | unclaimed | Current source retained verbatim; no adaptation in this packet. Prior sandbox copy removed on rebase, preserving independent withdrawals, quarantines and API repairs. |
| `Sheaf.AlgebraicGeometry.StrictHenselizationModuleFibreFactorization` | unclaimed | Replace the wrapper import with the same two upstream public imports. Replace each small-cone leg-equation call by choose_spec. |
| `Sheaf.AlgebraicGeometry.StrictHenselizationRestriction` | unclaimed | Current source retained verbatim; no adaptation in this packet. Prior sandbox copy removed on rebase, preserving independent withdrawals, quarantines and API repairs. |
| `Sheaf.AlgebraicGeometry.StrictLocalAlgebraicResidueModels` | unclaimed | Replace the wrapper import with the same two upstream public imports. |
| `Sheaf.AlgebraicGeometry.StrictLocalBaseChangeClosedStalk` | unclaimed | Current source retained verbatim; no adaptation in this packet. Prior sandbox copy removed on rebase, preserving independent withdrawals, quarantines and API repairs. |
| `Sheaf.AlgebraicGeometry.StrictLocalBaseChangeModelGlobalHomology` | unclaimed | Current source retained verbatim; no adaptation in this packet. Prior sandbox copy removed on rebase, preserving independent withdrawals, quarantines and API repairs. |
| `Sheaf.AlgebraicGeometry.StrictLocalCoefficientChart` | unclaimed | Replace the wrapper import with the same two upstream public imports. |
| `Sheaf.AlgebraicGeometry.StrictLocalCoefficientPresentation` | unclaimed | Replace the wrapper import with the same two upstream public imports. |
| `Sheaf.AlgebraicGeometry.StrictLocalGermRestrictionIso` | unclaimed | Current source retained verbatim; no adaptation in this packet. Prior sandbox copy removed on rebase, preserving independent withdrawals, quarantines and API repairs. |
| `Sheaf.AlgebraicGeometry.StrictLocalNeighbourhoodGeometry` | unclaimed | Replace the wrapper import with the same two upstream public imports. |
| `Sheaf.AlgebraicGeometry.StrictLocalRationalChart` | unclaimed | Replace the wrapper import with the same two upstream public imports. |
| `Sheaf.AlgebraicGeometry.StrictLocalSectionCone` | unclaimed | Replace the wrapper import with the same two upstream public imports. Replace each small-cone leg-equation call by choose_spec. |
| `Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalLocalizedHomGerm` | unclaimed | Current source retained verbatim; no adaptation in this packet. Prior sandbox copy removed on rebase, preserving independent withdrawals, quarantines and API repairs. |
| `Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalSectionsUnitLeray` | unclaimed | Replace the wrapper import with the same two upstream public imports. |
| `Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalUnderivedSectionsMate` | unclaimed | Current source retained verbatim; no adaptation in this packet. Prior sandbox copy removed on rebase, preserving independent withdrawals, quarantines and API repairs. |
| `Sheaf.Paper.StrictHenselizationFunctoriality` | unclaimed | Replace the wrapper import with the same two upstream public imports. Replace each small-cone leg-equation call by choose_spec. |
| `Sheaf.Paper.StrictHenselizationMapExists` | unclaimed | Replace the wrapper import with the same two upstream public imports. Replace each small-cone leg-equation call by choose_spec. |
| `Sheaf.TraceFormula.BoundedDimensionProjectiveLocalModel` | unclaimed | Replace the wrapper import with the same two upstream public imports. |
| `Sheaf.TraceFormula.SmoothGeometricStalkAlgebra` | unclaimed | Replace the wrapper import with the same two upstream public imports. |
| `Sheaf.AlgebraicGeometry.StrictLocalCohomologyGerms` | unclaimed | Mentions AlgebraicGeometry.Etale.strictLocalNeighbourhoodSection. Its data and type are unchanged; only the equality proof in the section construction changes to the identical choose_spec term. No source adaptation required. |
| `Sheaf.AlgebraicGeometry.StrictLocalConstantComparison` | unclaimed | Mentions AlgebraicGeometry.Etale.strictLocalNeighbourhoodSection. Its data and type are unchanged; only the equality proof in the section construction changes to the identical choose_spec term. No source adaptation required. |

The previous packet's G3 affine-chart adaptation is now omitted because the
current module is independently withdrawn. The M1 regularity module and the R4
Noetherian module keep their current upstream colimit-comparison proofs verbatim.
No equation for the upstream affine cone is replaced.

Return repair for head 19d77ccdb (reviewer C-19d77): the returned head adapted
`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationFinite`, held by M2,
and `Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationGenericEtale`,
held by G8. Rebasing on current shared sources eliminates both adaptations:
the current originals already publicly import the upstream StructuralMap owner,
use choose_spec directly, and contain complete small-colimit comparison helpers.
Their old sandbox copies would delete those helpers and revert their proof route.
Those copies are excluded entirely. Changed lines in both modules: none.
There is therefore no forced compiler error to claim for these current originals.
The unmodified originals compile on the server against an empty-wrapper overlay:
Finite in 12.2 s and GenericEtale in 0.1 s (exit code 0). The report records these
original-against-withdrawal checks.

The same rebase excludes the now-withdrawn CompatibleStrictHenselizationResidueLift
module instead of restoring its former R8 proof, and removes unnecessary stale
adaptations of RegularDivisorStrictHenselRootSection, StrictHenselRootFiniteEtaleModel,
StrictHenselRootPurityData and StrictHenselRootTameNormalization. Each current source
already uses the upstream owner. No declarations or public imports in those modules
are changed. All remaining adaptations migrate current wrapper importers or replace
its small-cone equation by the identical choose_spec term.

## Status

landed 20261021T162748-L-716953 2026-10-21 (merge of deliver/M4/Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap)
