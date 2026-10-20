# AlgebraicGeometry.etaleFieldGsets

## Reason

Retire the duplicate Sheaf module under the human's 2026-10-20 hand-off in
coord/changes/retire-sheaf-twins-20261020.md. The classification theorem already
exists upstream with the same signature and proof. The two additional global
instances of the Sheaf copy have definitionally identical upstream instances,
AlgebraicGeometry.etaleFieldDiscreteForget₂ and
AlgebraicGeometry.etaleFieldActionForget₂, which upstream marks local.
The consumers register those existing declarations as instances, preserving the
interface for themselves and their transitive consumers without duplicating data.
No upstream file, target statement, theorem statement or definition body changes.
All existing consumer proofs are retained. No proof is replaced by sorry.
The earlier A9 re-export packet is superseded by this full retirement.

## Old

The 14 direct consumers each contained this public import:

```lean
public import Sheaf.AlgebraicGeometry.EtaleFieldGsets
```

The deleted copy supplied these two global instances (verbatim):

```lean
instance hasForget₂TypeTopCat : HasForget₂ (Type u) TopCat :=
  ⟨TopCat.discrete, rfl⟩

instance hasForget₂DiscreteContActionType (G : Type*) [Monoid G] [TopologicalSpace G] :
    HasForget₂ (DiscreteContAction (Type u) G) (Type u) :=
  HasForget₂.trans (DiscreteContAction (Type u) G) (ContAction (Type u) G) (Type u)
```

Its classification theorem AlgebraicGeometry.etaleFieldGsets is identical to the
one in WeilConjectures.AlgebraicGeometry.EtaleFieldGsets modulo these instance names.

## New

Every direct consumer instead contains:

```lean
public import WeilConjectures.AlgebraicGeometry.EtaleFieldGsets
```

After its existing public-section command, each consumer registers the corresponding
upstream instances. The global attribute preserves instance synthesis in transitive
importers, including modules not edited by this packet:

```lean
attribute [instance] AlgebraicGeometry.etaleFieldDiscreteForget₂
  AlgebraicGeometry.etaleFieldActionForget₂
```

A documentation reference in Sites.EtaleSheavesGsetsPoint now uses the upstream
instance name. All other declaration text is unchanged. The old module is listed
in deleted.txt and is absent from the sandbox. The node lem-exc-etale-field-gsets
points to the upstream module and file, retaining the declaration and proof plan.

## Users

The full 47-module downstream closure and the current holders are listed below.
Only the 14 direct consumers change. The other two modules present under sandbox
lean/ are unchanged compilation intermediaries, not source adaptations.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AbelianSheavesGModules | unclaimed | Import the upstream twin; register its existing forgetful instances. |
| Sheaf.AlgebraicGeometry.AbelianSheavesGModulesAction | unclaimed | Import the upstream twin; register its existing forgetful instances. |
| Sheaf.AlgebraicGeometry.AbelianSheavesGModulesData | unclaimed | Import the upstream twin; register its existing forgetful instances. |
| Sheaf.AlgebraicGeometry.AbelianSheavesGModulesTransport | unclaimed | Import the upstream twin; register its existing forgetful instances. |
| Sheaf.AlgebraicGeometry.BaseFieldCohomologicalDimension | unclaimed | Receives the same forgetful functors transitively; no source edit. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteCoarseTraceFiltrationData | unclaimed | Receives the same forgetful functors transitively; no source edit. |
| Sheaf.AlgebraicGeometry.Curve.GenericFinitePrimaryDecomposition | unclaimed | Receives the same forgetful functors transitively; no source edit. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Receives the same forgetful functors transitively; no source edit. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Receives the same forgetful functors transitively; no source edit. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteTraceFiltrationData | unclaimed | Receives the same forgetful functors transitively; no source edit. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimaryAnnihilator | unclaimed | Receives the same forgetful functors transitively; no source edit. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimaryCoarseFiltrationCore | unclaimed | Receives the same forgetful functors transitively; no source edit. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimaryCoarseFiltrationData | unclaimed | Receives the same forgetful functors transitively; no source edit. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimaryCoarseTraceRetraction | unclaimed | Receives the same forgetful functors transitively; no source edit. |
| Sheaf.AlgebraicGeometry.EtaleGaloisUnitsComparison | unclaimed | Receives the same forgetful functors transitively; no source edit. |
| Sheaf.AlgebraicGeometry.EtaleModuleAffineBound | unclaimed | Receives the same forgetful functors transitively; no source edit. |
| Sheaf.AlgebraicGeometry.EtaleStalkContinuousCohomology | unclaimed | Receives the same forgetful functors transitively; no source edit. |
| Sheaf.AlgebraicGeometry.EtaleUnitsH2ForwardEmbedding | unclaimed | Receives the same forgetful functors transitively; no source edit. |
| Sheaf.AlgebraicGeometry.EtaleUnitsH2ReverseEmbedding | unclaimed | Receives the same forgetful functors transitively; no source edit. |
| Sheaf.AlgebraicGeometry.EtaleUnitsTwoCocycleComparison | unclaimed | Receives the same forgetful functors transitively; no source edit. |
| Sheaf.AlgebraicGeometry.FieldDiscreteModules | unclaimed | Receives the same forgetful functors transitively; no source edit. |
| Sheaf.AlgebraicGeometry.FiniteClassicalUnboundedComparison | unclaimed | Receives the same forgetful functors transitively; no source edit. |
| Sheaf.AlgebraicGeometry.GaloisPartitionExactRefinement | unclaimed | Receives the same forgetful functors transitively; no source edit. |
| Sheaf.AlgebraicGeometry.GaloisStalkActionEssSurj | unclaimed | Import the upstream twin; register its existing forgetful instances. |
| Sheaf.AlgebraicGeometry.GaloisStalkActionFull | unclaimed | Import the upstream twin; register its existing forgetful instances. |
| Sheaf.AlgebraicGeometry.GaloisStalkActionFullyFaithful | unclaimed | Import the upstream twin; register its existing forgetful instances. |
| Sheaf.AlgebraicGeometry.GaloisStalkActionFunctor | unclaimed | Import the upstream twin; register its existing forgetful instances. |
| Sheaf.AlgebraicGeometry.GaloisStalkFiniteActionRealization | unclaimed | Import the upstream twin; register its existing forgetful instances. |
| Sheaf.AlgebraicGeometry.GeometricPointDerivedConstants | unclaimed | Receives the same forgetful functors transitively; no source edit. |
| Sheaf.AlgebraicGeometry.GeometricPointDerivedSectionsAdjunction | P5 | Receives the same forgetful functors transitively; no source edit. |
| Sheaf.AlgebraicGeometry.GeometricPointProjectionComparison | W4 | Receives the same forgetful functors transitively; no source edit. |
| Sheaf.AlgebraicGeometry.ProEtaleClassicalBounds | unclaimed | Receives the same forgetful functors transitively; no source edit. |
| Sheaf.AlgebraicGeometry.Sites.EtaleSheavesGsetsPoint | unclaimed | Import the upstream twin; register its existing forgetful instances. |
| Sheaf.AlgebraicGeometry.Sites.FiniteFieldTorsionCohomologicalDimension | unclaimed | Receives the same forgetful functors transitively; no source edit. |
| Sheaf.AlgebraicGeometry.UnboundedDirectImageComparison | unclaimed | Receives the same forgetful functors transitively; no source edit. |
| Sheaf.AlgebraicGeometry.UnboundedDirectImageTruncationStability | unclaimed | Receives the same forgetful functors transitively; no source edit. |
| Sheaf.AlgebraicGeometry.UnboundedSiteComparison | unclaimed | Receives the same forgetful functors transitively; no source edit. |
| Sheaf.CategoryTheory.DiscreteContActionFiniteOrbitCoproduct | Y3 | Import the upstream twin; register its existing forgetful instances. |
| Sheaf.CategoryTheory.DiscreteContinuousRepCommGrp | unclaimed | Import the upstream twin; register its existing forgetful instances. |
| Sheaf.CategoryTheory.DiscreteContinuousRepCommGrpAux | unclaimed | Import the upstream twin; register its existing forgetful instances. |
| Sheaf.CategoryTheory.DiscreteContinuousRepToCommGrp | K9 | Import the upstream twin; register its existing forgetful instances. |
| Sheaf.CategoryTheory.DiscreteContinuousRepToCommGrpEssSurj | unclaimed | Receives the same forgetful functors transitively; no source edit. |
| Sheaf.CategoryTheory.DiscreteContinuousRepToCommGrpFull | unclaimed | Receives the same forgetful functors transitively; no source edit. |
| Sheaf.Paper.CtfHomLocallyConstant | unclaimed | Receives the same forgetful functors transitively; no source edit. |
| Sheaf.Paper.FiniteRingCompactSupportProjection | unclaimed | Receives the same forgetful functors transitively; no source edit. |
| Sheaf.RepresentationTheory.NormalSubgroupIndUnipotence | unclaimed | Receives the same forgetful functors transitively; no source edit. |
| Sheaf.SixFunctors.ClassicalModuleAffineEvaluationBound | unclaimed | Receives the same forgetful functors transitively; no source edit. |

## Status

landed 20261020T144234-L-2257712 2026-10-20 (merge of deliver/A9/Sheaf.AlgebraicGeometry.EtaleFieldGsets)
(dry-run commit `2ad6c2783f5`); pending delivery, independent CODEX review and
global-build verification. All 14 adapted consumers and both unchanged
compilation intermediaries compile without errors or warnings. No holes added.
The earlier delivery counterfactual refusal is resolved: the launcher now
accounts for explicitly withdrawn dependencies in `deleted.txt`.
