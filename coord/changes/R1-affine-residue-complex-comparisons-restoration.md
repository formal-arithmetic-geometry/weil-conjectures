# Affine residue complex comparisons and quarantine restoration

## Reason

Restore `Sheaf.AlgebraicGeometry.AffineFreeResidueSectionsDerivedModel` from the archive
named by its current rework row. Its public theorem and all three dependencies remain.
The archived proof has zero holes and its cohomology consumer still applies it.

The required dependency `Sheaf.AlgebraicGeometry.AffineKFlatResiduePullbackModel` is
present in source but was not available in the published build. A direct unchanged
single-file compile exceeded 60 seconds. Profiling and a signature-only diagnostic
isolated expensive definitional comparisons in its complex-isomorphism assembly.
`Functor.mapHomologicalComplex` preserves functor composition definitionally, so the
identity composition isomorphisms surrounding `NatIso.mapHomologicalComplex` are
unnecessary. Remove them from the private helper, its restriction comparison, and
the restored item. The final simplified dependency, including the complete maintainer axiom probe,
compiled in 48.9 seconds (`SHEAF-PROBED 2`, no disallowed axioms or holes).
The restored item compiled in 29.6 seconds.
No timeout or heartbeat limit is raised, no proof is split, and no data construction,
public signature, visibility, instance, attribute or public import changes.

## Old

The assigned module is absent from `lean/`; its original statement and complete
proof are preserved at
`quarantine/Sheaf/AlgebraicGeometry/AffineFreeResidueSectionsDerivedModel.lean`.
The dependency's private helper was:

```lean
private noncomputable def mapComplexComparison
    {C D E H J : Type*} [Category* C] [Category* D] [Category* E]
    [Category* H] [Category* J] [Preadditive C] [Preadditive D] [Preadditive E]
    [Preadditive H] [Preadditive J]
    (A : C ⥤ D) (B : D ⥤ E) (S : C ⥤ H) (R : H ⥤ J) (L : J ⥤ E)
    [A.Additive] [B.Additive] [S.Additive] [R.Additive] [L.Additive]
    (α : A ⋙ B ≅ (S ⋙ R) ⋙ L) (F : CochainComplex C ℤ) :
    (B.mapHomologicalComplex (.up ℤ)).obj ((A.mapHomologicalComplex (.up ℤ)).obj F) ≅
      (L.mapHomologicalComplex (.up ℤ)).obj
        ((R.mapHomologicalComplex (.up ℤ)).obj ((S.mapHomologicalComplex (.up ℤ)).obj F)) :=
  ((Functor.mapHomologicalComplexCompIso (Iso.refl (A ⋙ B)) (.up ℤ)).app F).symm ≪≫
    (NatIso.mapHomologicalComplex α (.up ℤ)).app F ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl ((S ⋙ R) ⋙ L)) (.up ℤ)).app F ≪≫
    (L.mapHomologicalComplex (.up ℤ)).mapIso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (S ⋙ R)) (.up ℤ)).app F)
```

The restriction comparison in its public theorem also surrounded the induced
natural isomorphism by two `mapHomologicalComplexCompIso (Iso.refl ...)` components.

## New

Restore the archived public theorem with exactly its original signature and imports.
Its final scalar-transport comparison is now the direct component of the induced
natural isomorphism. The dependency's private helper becomes:

```lean
private noncomputable def mapComplexComparison
    {C D E H J : Type*} [Category* C] [Category* D] [Category* E]
    [Category* H] [Category* J] [Preadditive C] [Preadditive D] [Preadditive E]
    [Preadditive H] [Preadditive J]
    (A : C ⥤ D) (B : D ⥤ E) (S : C ⥤ H) (R : H ⥤ J) (L : J ⥤ E)
    [A.Additive] [B.Additive] [S.Additive] [R.Additive] [L.Additive]
    (α : A ⋙ B ≅ (S ⋙ R) ⋙ L) (F : CochainComplex C ℤ) :
    (B.mapHomologicalComplex (.up ℤ)).obj ((A.mapHomologicalComplex (.up ℤ)).obj F) ≅
      (L.mapHomologicalComplex (.up ℤ)).obj
        ((R.mapHomologicalComplex (.up ℤ)).obj ((S.mapHomologicalComplex (.up ℤ)).obj F)) :=
  (NatIso.mapHomologicalComplex α (.up ℤ)).app F
```

The two local additive proofs now apply `Adjunction.left_adjoint_additive`
directly, avoiding construction of finite-colimit preservation just to recover
additivity. The same adjunctions and functors are used.

The restriction comparison `ε` likewise becomes
`(NatIso.mapHomologicalComplex δ (.up ℤ)).app F`. All endpoints are definitionally
identical to the originals, as checked by Lean against the unchanged signatures.
The assigned node retains its attachment and dependency list, with step 3 updated
to describe this direct comparison. No definition used by a target changes meaning.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.AffineKFlatResiduePullbackModel
--uses mapComplexComparison` reports only the dependency itself: its helper is private.
A separate source import-graph check including quarantined modules finds the consumers
below. Their signatures and proofs remain applicable because the public theorem types
and public imports do not change. Only the two named modules are delivered. The archived direct consumer
`AffineFreeResidueSectionsCohomology` was compiled unchanged against the new sandbox
outputs and passed in 18.8 seconds; no consumer adaptation was needed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineBettiModelResidueMinimality | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineBoundedAboveFiberBettiComparison | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineFreeResidueSectionsCohomology | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineFreeResidueSectionsDerivedModel | R1 | Restored with the original public interface; direct scalar comparison. |
| Sheaf.AlgebraicGeometry.AffineKFlatResiduePullbackModel | unclaimed | Private comparison implementation simplified; public interface unchanged. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectJumpLoci | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectLowestCohomologyLocus | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectLowestRankBoundOpen | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberDirectImageRankConstructible | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1CommonMinimalModel | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparison | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparisonSource | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparisonTargets | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologySourceResidueComparison | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueSourceModelHomology | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchFixedRankRetrocompact | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCore | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCoreRank | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationCore | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationIso | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusLocallyFinitePresentation | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusQuasiCompact | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocusFinitePresentation | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PseudoCoherentFiberBoundedAboveModel | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.PseudoCoherentFiberFiniteFreeModel | unclaimed | Original public interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.ResidueRankModelDifferential | unclaimed | Original public interface preserved; no adaptation. |

## Status

landed 20261020T230826-L-617699 2026-10-20 (merge of deliver/R1/Sheaf.AlgebraicGeometry.AffineFreeResidueSectionsDerivedModel)
