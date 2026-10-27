# WeilConjectures.CompletedLineTensor.comparisonComplex

## Reason

The original definition spends about eight seconds in kernel conversion of a mapped
composite functor to a composite of mapped functors. Elaborate that same conversion
once with abstract category and functor parameters in a local `let`. The resulting
value is definitionally equal to the old value by zeta and beta reduction. No
signature, universe, attribute or public import changes, and no new datum is chosen.

The existing scalar-identity construction is also extracted into
`CompletedScalarIdentityUnit`; its former parent retains the good-complex uniqueness
argument. This changes only theorem proofs and adds no pending statement.

The new proof sections and Mathlib sheafification projection priority are local
elaboration settings. They do not export instances or transparency changes.

## Old

```lean
def comparisonComplex (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X) [N.IsFiniteLocallyFreeOfRank 1] (m : ℤ)
    (e : sheaf l E X L m ⋙ completedOrdinaryScalarExtension l E F ι X ≅
      completedOrdinaryScalarExtension l E F ι X ⋙ sheaf l F X N m) :
    complex l E X L m ⋙ completedOrdinaryScalarComplex l E F ι X ≅
      completedOrdinaryScalarComplex l E F ι X ⋙ complex l F X N m :=
  by
    unfold complex completedOrdinaryScalarComplex
    exact NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)
```

The old point-normalization module contained both its model definitions and all
proved auxiliaries (lines 1–520), followed by its final theorem.

## New

```lean
def comparisonComplex (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X) [N.IsFiniteLocallyFreeOfRank 1] (m : ℤ)
    (e : sheaf l E X L m ⋙ completedOrdinaryScalarExtension l E F ι X ≅
      completedOrdinaryScalarExtension l E F ι X ⋙ sheaf l F X N m) :
    complex l E X L m ⋙ completedOrdinaryScalarComplex l E F ι X ≅
      completedOrdinaryScalarComplex l E F ι X ⋙ complex l F X N m :=
  by
    unfold complex completedOrdinaryScalarComplex
    let lift {A B C D : Type (max (t + 2) (u + 1))}
        [Category.{max (t + 1) u} A] [Category.{max (t + 1) u} B]
        [Category.{max (t + 1) u} C] [Category.{max (t + 1) u} D]
        [HasZeroMorphisms A] [HasZeroMorphisms B]
        [HasZeroMorphisms C] [HasZeroMorphisms D]
        (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
        [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
        [H.PreservesZeroMorphisms] [I.PreservesZeroMorphisms]
        (e : F ⋙ G ≅ H ⋙ I) :
        F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) ≅
          H.mapHomologicalComplex (.up ℤ) ⋙ I.mapHomologicalComplex (.up ℤ) :=
      NatIso.mapHomologicalComplex e (.up ℤ)
    exact lift _ _ _ _ e

```

The unchanged point models and proved auxiliaries are in
`lean/Sheaf/Paper/PointEvaluationCompletionModels.lean`. The original module
adds a public import of that module and imports its private auxiliary proofs with
`import all`; it retains the exact final theorem and its proof. Local elaboration
settings are repeated as needed without changing exported attributes.

The consumer `PointCompletedEvaluation` adds only:

```lean
set_option Elab.async false
attribute [local instance 5000] CategoryTheory.HasSheafify.isRightAdjoint
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedLineTensorCoherence | H1 | Same definition by reduction; faster conversion. |
| Sheaf.Paper.PointSystemTransportDescent | unclaimed | Textual short-name match is its unrelated local definition. |
| Sheaf.Paper.AdicOperationDomainsSourceComparison | unclaimed | Unchanged direct importer; verification only. |
| Sheaf.Paper.CompactSupportNormalizedScalarDescent | unclaimed | Unchanged direct importer; verification only. |
| Sheaf.Paper.FdIntegralInverseScalarCocycle | unclaimed | Unchanged direct importer; verification only. |
| Sheaf.Paper.IntegralLineTensorCompleteness | unclaimed | Unchanged direct importer; verification only. |
| Sheaf.Paper.IntegralTwistAmbientCoherence | unclaimed | Unchanged direct importer; verification only. |
| Sheaf.Paper.IntegralTwistCommonScalarModel | unclaimed | Unchanged direct importer; verification only. |
| Sheaf.Paper.IntegralTwistScalarCoherence | unclaimed | Unchanged direct importer; verification only. |
| Sheaf.Paper.MixedReductionUnitComposition | unclaimed | Unchanged direct importer; verification only. |
| Sheaf.Paper.PerfectDualPairAndTateStability | unclaimed | Unchanged direct importer; verification only. |
| Sheaf.Paper.PointEvaluationCompletionNormalization | unclaimed | Existing models and proved private lemmas moved verbatim to PointEvaluationCompletionModels; final theorem retained. |
| Sheaf.Paper.PointEvaluationCompletionModels | new | Verbatim extraction with zero holes. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | Synchronous elaboration and local adjunction-projection priority only; no interface or body change. |
| Sheaf.Paper.PointSectionsCompletionCone | unclaimed | Unchanged direct importer; verification only. |
| Sheaf.Paper.PurShiftedTateUnitScalarCoherence | unclaimed | Unchanged direct importer; verification only. |
| Sheaf.Paper.ScalarCompletionAssociator | unclaimed | Unchanged direct importer; verification only. |
| Sheaf.Paper.ScalarShiftLineTowerTransport | unclaimed | Unchanged direct importer; verification only. |
| Sheaf.Paper.TateTwistIntegralLines | unclaimed | Unchanged direct importer; verification only. |
| Sheaf.Paper.TateTwistLocallyFree | unclaimed | Unchanged direct importer; verification only. |
| Sheaf.Paper.UnshiftedLineUnitTower | unclaimed | Unchanged direct importer; verification only. |
| Sheaf.Paper.WfTateTwistCompatibility | unclaimed | Unchanged direct importer; verification only. |
| Sheaf.TraceFormula.CounitRealizationSubstitution | unclaimed | Unchanged direct importer; verification only. |
| Sheaf.TraceFormula.ScalarModelAssociativity | unclaimed | Unchanged direct importer; verification only. |
| Sheaf.TraceFormula.ScalarModelIteratedStrictCalculation | unclaimed | Unchanged direct importer; verification only. |
| Sheaf.TraceFormula.ScalarModelUnit | claimed | Unchanged direct importer; verification only. |

There are no external textual uses of this qualified declaration. All direct importers
are checked against the changed module. The point-normalization importer originally
exceeded the file limit at 68 seconds. Its existing model definitions and proved private auxiliary lemmas are extracted
verbatim into `Sheaf.Paper.PointEvaluationCompletionModels`. The original module
publicly reexports them and retains its original final theorem statement and proof.
Existing public imports, declaration names, signatures, data bodies and attributes
are retained. The original point node retains its final theorem, and the new
`def-pod-point-evaluation-completion-models` node records the moved declarations.
The mathematical proof route is unchanged. A baseline check against the published
library also exceeded the limit (105 seconds), so this extraction addresses an
existing performance issue as well. Its sole direct importer,
`Sheaf.Paper.PointCompletedEvaluation`, is checked as well; its original source exceeded the file limit at 65 seconds. Only synchronous
elaboration and a local priority for the existing sheafification adjunction
projection are added. All declaration statements and bodies, public imports and
exported attributes remain unchanged.

## Status

landed 20261027T151710-L-1194234 2026-10-27 (merge of deliver/H1/Sheaf.Paper.CompletedLineTensorCoherence)
