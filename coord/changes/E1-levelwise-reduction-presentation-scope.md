# Sheaf.Paper.LevelwiseAdicTruncations restored proof compilation

## Reason

Repair 48160399e7852af6 returned the G1 proof packet after its public
pbcAdicCompletion alias change broke four global-build consumers. Restore the
complete mathematical proofs and their seven helper modules without changing that
public alias. The original coefficient presentation is definitionally equal to
completedReductionCoefficient, but the item's file-wide local irreducibility prevents
the necessary category conversion in its reduction-tower block.

Keep the chosen limit construction irreducible while permitting conversion of the
coefficient aliases in that block. Replace broad simplification of complete tower
witnesses in construct_truncations with their explicit endpoint equalities.
This repairs elaboration without changing a mathematical statement or data construction.

## Old

The local attribute

```lean
attribute [local irreducible] Functor.mapDerivedCategory completedReductionCoefficient
```

applied throughout the reduction-tower block of the returned complete proof packet.
The private reduction_allpair_comparison ended in its naturality rewrite. The two
constructor endpoint proofs were:

```lean
    · simp [PbcLevelwiseTruncationData.lowerNormalization, N, L]
    · simp [PbcLevelwiseTruncationData.upperNormalization, N, U]
```

## New

Enclose pbcReductionEvaluationIso through pbcReductionAdicTower in this local scope:

```lean
section ReductionTowerPresentation
attribute [local semireducible] completedReductionCoefficient
attribute [local irreducible] CategoryTheory.Limits.limit
-- Existing declarations and data constructions.
end ReductionTowerPresentation
```

The private comparison's naturality rewrite is followed by rfl. The two constructor
endpoint proofs explicitly change the goal to composition of the appropriate
triangle component with identity isomorphisms, then use only
Functor.mapIso_refl, Iso.refl_hom, Category.id_comp and Category.comp_id.

The following original public definition in BoundedConstructibleTower stays verbatim:

```lean
abbrev pbcAdicCompletion (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) :=
  AdicCoefficients.completedRing X d.ideal d.quotientFinite
```

That module and its node are not delivered. The failed G1 alias change is not restored.
All existing public signatures and definition bodies remain unchanged. Relative to the
post-rollback source, private proof imports and seven proved supporting modules are
restored; report.md and the parent node describe that mathematical argument.
No target meaning changes and no target re-review is needed for a definition change.

## Users

These are the direct source importers of the item. Its public signatures and data
constructions are unchanged, so no adaptation is required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicSuppliedModelFlatCriterion | unclaimed | No adaptation. |
| Sheaf.Paper.PbcUniformReductionCriterion | unclaimed | No adaptation. |
| Sheaf.Paper.PbcUniformLocalModelCohomology | unclaimed | No adaptation. |
| Sheaf.Paper.AdicTorFlatCriterion | unclaimed | No adaptation. |
| Sheaf.Paper.AdicCohomologyTorsionNormalForm | unclaimed | No adaptation. |
| Sheaf.Paper.AdicTorFlatCohomology | unclaimed | No adaptation. |

The four original modules named by the global-build return compile unchanged:
CompletedPullbackReduction (56.9 seconds), CompletedTowerDirectImage (30.4),
FiniteExtensionReductionConeBound (9.3), PerfectChartTensorComparison (28.9).
Their temporary verification copies are not delivered. No forced adaptation is needed.

The seven restored helper modules compile cleanly. The full item with both local
elaboration repairs compiles cleanly in 39.2 seconds. No resource limit is raised;
no diagnostic option or diagnostic module remains in the delivery.

## Status

landed 20261022T040155-L-2822089 2026-10-22 (merge of deliver/E1/Sheaf.Paper.LevelwiseAdicTruncations)
