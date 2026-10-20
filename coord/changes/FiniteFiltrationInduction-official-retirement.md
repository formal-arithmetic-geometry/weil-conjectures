# CategoryTheory.FilteredObject finite filtration induction retirement

## Reason

The assigned module is listed as a retirement item in coord/retire-items.tsv and has
zero holes. The adopted source library now provides its complete API in
WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension. The declaration
sections, from `@[expose] public section` through the final `end CategoryTheory`,
are byte-for-byte identical. This includes the two constructions, both public
theorems, every private helper, every signature, every docstring and every proof.
Retaining both copies risks duplicate declarations when their import closures meet.

The retirement inventory points to WeilConjectures.CategoryTheory.FiniteFiltrationInduction,
whose API uses different names and still has two holes. That is not the replacement
used here. FiniteFiltrationInductionExtension provides the exact existing step API,
with complete proofs and no additional assumptions.

The proof remains the existing cokernel construction and descending induction via
Mathlib's short five lemma. Both lower and upper integer bounds, and the conclusion
for every filtration step, stay unchanged. Zero objects and empty or degenerate
filtration intervals introduce no new restriction. No target changes its meaning.

## Old

Each adapted consumer imports the duplicate with its original visibility:
```lean
public import Sheaf.CategoryTheory.FiniteFiltrationInduction
```
FiniteRangeComparison uses the proof import instead:
```lean
import Sheaf.CategoryTheory.FiniteFiltrationInduction
```
The four public signatures, retained verbatim in the replacement, are:
```lean
noncomputable def restrictionSteps {A B : FilteredObject C} (f : Hom A B) (p : ℤ) :
    (A.filtration.step p : C) ⟶ (B.filtration.step p : C)
theorem exists_gradedMap_steps (A B : FilteredObject C) (f : Hom A B) (p : ℤ) :
    ∃ g : A.filtration.gradedPiece p ⟶ B.filtration.gradedPiece p,
      cokernel.π (Subobject.ofLE (A.filtration.step (p + 1))
        (A.filtration.step p) (A.filtration.antitone_step (by omega))) ≫ g =
        restrictionSteps f p ≫ cokernel.π (Subobject.ofLE (B.filtration.step (p + 1))
          (B.filtration.step p) (B.filtration.antitone_step (by omega)))
noncomputable def gradedMapSteps {A B : FilteredObject C} (f : Hom A B) (p : ℤ) :
    A.filtration.gradedPiece p ⟶ B.filtration.gradedPiece p
theorem finite_filtration_induction_steps (A B : FilteredObject C) (f : Hom A B)
    (hA : A.filtration.IsFinite) (hB : B.filtration.IsFinite)
    (hgraded : ∀ p : ℤ, IsIso (gradedMapSteps f p)) :
    IsIso f.hom ∧ ∀ p : ℤ, IsIso (restrictionSteps f p)
```

## New

The duplicate is withdrawn using deleted.txt. Each of its eleven active direct
consumers replaces only that import with:
```lean
public import WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension
```
FiniteRangeComparison preserves its proof-only visibility:
```lean
import WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension
```
Every remaining line of each consumer is unchanged. No upstream file is changed.
The lem-sp-finite-filtration-induction node keeps its mathematical statement,
proof steps, proof dependencies, declaration names, and parent edges; its Lean
module/file attachment now names the adopted replacement. This preserves every
unfinished and quarantined parent's dependency, including the proper-base-change
unit route, rather than removing a needed mathematical result.

## Users

The refreshed source-only inventory includes active and quarantined transitive users,
with textual uses of all four public names checked. The eleven active
direct consumers are delivered and compiled together. Three additional direct
consumers remain in quarantine at their recorded paths. Their archives are
preserved; restoration must migrate the import to the identical replacement.
The two restored consumers that already import the replacement are also listed.

The return at head 4762cfb2c named SplitFlatFilteredSheafModels as a missing user.
Its gradedMapSteps use is supplied transitively through the adapted
UniformFiniteFilteredLocalization public import; no source edit is needed there.
The refreshed scan also finds FilteredDerivedHomCalculus and
FiniteFilteredFlatSheafResolution. FiniteFilteredLocalization has since been
restored, so its direct public import is migrated in this repair.
The push check then found the newly restored FiniteFilteredDerivedPresentation;
its direct public import is migrated too. The table includes the restored filtered-localization users.

The return at head 07e109615 named FilteredTensorLocalization and
FiniteFilteredKFlatReplacement. Both rows are now included explicitly, with their
graded-map and restriction-map uses checked against the preserved quarantine
archives. Their statements and definitions keep the exact same API. The inventory
also includes other current import descendants and textual API users, including
quarantined consumers; none of their archives or DAG attachments is withdrawn.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.BoundedAboveCoherentRHom | unclaimed | Same declarations from the replacement through adapted imports; no source edit is needed. |
| Sheaf.Algebra.Homology.BoundedAboveRHomHyperExt | unclaimed | Replace only the import; visibility, signatures, definitions and proofs are unchanged. |
| Sheaf.Algebra.Homology.CoherentRHomFiniteInjectiveDimension | unclaimed | Same declarations from the replacement through adapted imports; no source edit is needed. |
| Sheaf.Algebra.Homology.CompleteLocalCoherentDuality | unclaimed | Same declarations from the replacement through adapted imports; no source edit is needed. |
| Sheaf.Algebra.Homology.FilteredBoundedLocalizationComparison | unclaimed | Same declarations from the replacement through adapted imports; no source edit is needed. |
| Sheaf.Algebra.Homology.FilteredDerivedHomCalculus | unclaimed | Same gradedMapSteps declaration through the adapted FiniteFilteredLocalization public import; no source edit is needed. |
| Sheaf.Algebra.Homology.FiniteFilteredFlatSheafResolution | unclaimed | Same graded-map API through adapted transitive imports; no source edit is needed. |
| Sheaf.Algebra.Homology.FiniteFilteredLocalization | unclaimed | Restored since the returned packet; replace only the public import, preserving all signatures, definitions and proofs. |
| Sheaf.Algebra.Homology.SplitFlatFilteredSheafModels | unclaimed | Same gradedMapSteps declaration through the adapted UniformFiniteFilteredLocalization public import; no source edit is needed. |
| Sheaf.Algebra.Homology.SemidualizingRHomConservative | unclaimed | Same declarations from the replacement through adapted imports; no source edit is needed. |
| Sheaf.Algebra.Homology.UniformFiniteFilteredLocalization | unclaimed | Replace only the import; visibility, signatures, definitions and proofs are unchanged. |
| Sheaf.AlgebraicGeometry.FiniteRangeComparison | unclaimed | Replace only the import; visibility, signatures, definitions and proofs are unchanged. |
| Sheaf.CategoryTheory.BoundedBelowCoproductFiltration | unclaimed | Replace only the import; visibility, signatures, definitions and proofs are unchanged. |
| Sheaf.CategoryTheory.FilteredHomotopySpectralSequence | unclaimed/rework | Active on the current base and archived in the rework cluster; replace only the deleted-module import with the identical replacement, preserving all declarations, signatures and DAG attachments. |
| Sheaf.CategoryTheory.FilteredPageTwoComparison | unclaimed | Replace only the deleted-module import with the identical replacement; all declarations, signatures and proofs are unchanged. |
| Sheaf.CategoryTheory.FiniteFilteredColimitComparison | unclaimed | Replace only the import; visibility, signatures, definitions and proofs are unchanged. |
| Sheaf.CategoryTheory.FiniteFilteredColimitModel | unclaimed | Replace only the import; visibility, signatures, definitions and proofs are unchanged. |
| Sheaf.CategoryTheory.SpectralSequenceComparison | unclaimed | Replace only the import; visibility, signatures, definitions and proofs are unchanged. |
| Sheaf.Paper.ConstructibleRHomCoproductContinuity | unclaimed | Same declarations from the replacement through adapted imports; no source edit is needed. |
| Sheaf.Paper.FiniteFilteredGradedExactness | unclaimed | Replace only the import; visibility, signatures, definitions and proofs are unchanged. |
| Sheaf.CategoryTheory.FiniteFiltrationInduction | S3 | Withdraw duplicate and reattach its node to the identical proved replacement. |
| Sheaf.Paper.FlatFilteredComplexComparison | unclaimed | Restored in the current sheaf-dag base; replace only the deleted-module import with the identical replacement, preserving all declarations and signatures. |
| Sheaf.CategoryTheory.FiniteFilteredDerivedPresentation | unclaimed | Restored during this repair; replace only its public import with the identical replacement, preserving all definitions and signatures. |
| Sheaf.Algebra.Homology.FiniteFilteredModuleHomotopy | unclaimed | Restored and already imports the identical upstream replacement directly; no edit is needed. |
| Sheaf.Algebra.Homology.FilteredHomComplexInvariance | unclaimed | Restored and already imports the identical upstream replacement directly; no edit is needed. |
| Sheaf.Algebra.Homology.FilteredTensorGradedComparison (quarantined) | P1 | Archive preserved; restoration must import the replacement with the same visibility. All declarations and DAG dependencies remain available. |
| Sheaf.Algebra.Homology.BoundedFilteredLocalizationEmbedding | unclaimed | Restored since the previous scan; identical filtration API through migrated transitive imports, with no source edit needed. |
| Sheaf.Algebra.Homology.FilteredAcyclicInjectiveVanishing | unclaimed | Restored since the previous scan; identical filtration API through migrated transitive imports, with no source edit needed. |
| Sheaf.Algebra.Homology.FilteredConeLocalization | unclaimed | Restored since the previous scan; identical filtration API through migrated transitive imports, with no source edit needed. |
| Sheaf.Algebra.Homology.FilteredInjectiveResolution | unclaimed | Restored since the previous scan; identical filtration API through migrated transitive imports, with no source edit needed. |
| Sheaf.Algebra.Homology.FilteredLocalizationInjectiveModel | unclaimed | Restored since the previous scan; identical filtration API through migrated transitive imports, with no source edit needed. |
| Sheaf.Algebra.Homology.FilteredTruncationData | unclaimed | Restored since the previous scan; identical filtration API through migrated transitive imports, with no source edit needed. |
| Sheaf.Algebra.Homology.FilteredTruncationTriangle | unclaimed | Restored since the previous scan; identical filtration API through migrated transitive imports, with no source edit needed. |
| Sheaf.Algebra.Homology.UniformFilteredHomotopyLocalization | unclaimed | Restored since the previous scan; identical filtration API through migrated transitive imports, with no source edit needed. |
| Sheaf.Algebra.Homology.UniformFilteredTruncation | unclaimed | Restored since the previous scan; identical filtration API through migrated transitive imports, with no source edit needed. |
| Sheaf.AlgebraicGeometry.LocalizationFiltrationDescent | unclaimed | Restored since the previous scan; identical filtration API through migrated transitive imports, with no source edit needed. |
| Sheaf.AlgebraicGeometry.ProEtaleLocalizationFilteredSection | unclaimed | Restored since the previous scan; identical filtration API through migrated transitive imports, with no source edit needed. |
| Sheaf.CategoryTheory.FilteredBifunctorGradedComparison | unclaimed | Restored since the previous scan; identical filtration API through migrated transitive imports, with no source edit needed. |
| Sheaf.CategoryTheory.FilteredDerivedOperationLifts | unclaimed | Restored since the previous scan; identical filtration API through migrated transitive imports, with no source edit needed. |
| Sheaf.CategoryTheory.FilteredFunctorGradedComparison | unclaimed | Restored since the previous scan; identical filtration API through migrated transitive imports, with no source edit needed. |
| Sheaf.Paper.FiniteCoefficientDualConstructible | unclaimed | Restored since the previous scan; identical filtration API through migrated transitive imports, with no source edit needed. |
| Sheaf.Paper.HomUniversalCoefficients | unclaimed | Restored since the previous scan; identical filtration API through migrated transitive imports, with no source edit needed. |

| Sheaf.Algebra.Homology.BoundedTensorTorSpectralSequence | unclaimed | Quarantined archive and all DAG dependencies preserved. The identical replacement API remains available through migrated transitive imports on restoration; no edit is needed here. |
| Sheaf.Algebra.Homology.CanonicalTruncationFiltration | unclaimed | Same filtration API through the replacement or adapted transitive imports; all statements and definitions are unchanged, and no source edit is needed here. |
| Sheaf.Algebra.Homology.DerivedCanonicalFiltration | unclaimed | Quarantined archive and all DAG dependencies preserved. The identical replacement API remains available through migrated transitive imports on restoration; no edit is needed here. |
| Sheaf.Algebra.Homology.FilteredDerivedHomCalculusUniverse | unclaimed | Quarantined archive and all DAG dependencies preserved. The identical replacement API remains available through migrated transitive imports on restoration; no edit is needed here. |
| Sheaf.Algebra.Homology.FilteredGlobalHomExactAdjunction | unclaimed | Quarantined archive and all DAG dependencies preserved. The identical replacement API remains available through migrated transitive imports on restoration; no edit is needed here. |
| Sheaf.Algebra.Homology.FilteredPageLocalization | M8 | Same filtration API through the replacement or adapted transitive imports; all statements and definitions are unchanged, and no source edit is needed here. |
| Sheaf.Algebra.Homology.FilteredQuasiIsoTwoOutOfThree | unclaimed | Same filtration API through the replacement or adapted transitive imports; all statements and definitions are unchanged, and no source edit is needed here. |
| Sheaf.Algebra.Homology.FilteredTensorLocalization | unclaimed | Quarantined archive preserved. Its gradedMapSteps use receives the identical replacement API through FiniteFilteredModuleHomotopy and the restored filtered-tensor imports; no declaration or source edit is needed here. |
| Sheaf.Algebra.Homology.FiniteFilteredKFlatReplacement | unclaimed | Quarantined archive preserved. Its restrictionSteps and gradedMapSteps uses receive the identical replacement API through FiniteFilteredModuleHomotopy; no declaration or source edit is needed here. |
| Sheaf.Algebra.Homology.IntegralBoundedKunnethExact | unclaimed | Quarantined archive and all DAG dependencies preserved. The identical replacement API remains available through migrated transitive imports on restoration; no edit is needed here. |
| Sheaf.AlgebraicGeometry.AbelianArbitrarySchemeUntensoredBaseChange | unclaimed | Quarantined archive and all DAG dependencies preserved. The identical replacement API remains available through migrated transitive imports on restoration; no edit is needed here. |
| Sheaf.AlgebraicGeometry.ArbitrarySchemeUntensoredBaseChange | unclaimed | Quarantined archive and all DAG dependencies preserved. The identical replacement API remains available through migrated transitive imports on restoration; no edit is needed here. |
| Sheaf.AlgebraicGeometry.IntegralDerivedTensorBoundedTorsion | unclaimed | Quarantined archive and all DAG dependencies preserved. The identical replacement API remains available through migrated transitive imports on restoration; no edit is needed here. |
| Sheaf.AlgebraicGeometry.IntegralProperProjectionFormula | unclaimed | Quarantined archive and all DAG dependencies preserved. The identical replacement API remains available through migrated transitive imports on restoration; no edit is needed here. |
| Sheaf.AlgebraicGeometry.KunnethMapAgrees | unclaimed | Quarantined archive and all DAG dependencies preserved. The identical replacement API remains available through migrated transitive imports on restoration; no edit is needed here. |
| Sheaf.AlgebraicGeometry.NormalGenericFibreVanishing | unclaimed | Quarantined archive and all DAG dependencies preserved. The identical replacement API remains available through migrated transitive imports on restoration; no edit is needed here. |
| Sheaf.AlgebraicGeometry.OpenProductExchange | unclaimed | Quarantined archive and all DAG dependencies preserved. The identical replacement API remains available through migrated transitive imports on restoration; no edit is needed here. |
| Sheaf.AlgebraicGeometry.PrimeTorsionCoefficientReduction | unclaimed | Quarantined archive and all DAG dependencies preserved. The identical replacement API remains available through migrated transitive imports on restoration; no edit is needed here. |
| Sheaf.AlgebraicGeometry.ProperKunnethGlobalSections | unclaimed | Quarantined archive and all DAG dependencies preserved. The identical replacement API remains available through migrated transitive imports on restoration; no edit is needed here. |
| Sheaf.AlgebraicGeometry.PunctualTensorBaseChange | unclaimed | Quarantined archive and all DAG dependencies preserved. The identical replacement API remains available through migrated transitive imports on restoration; no edit is needed here. |
| Sheaf.AlgebraicGeometry.RelativeDualizingPairRigidity | unclaimed | Quarantined archive and all DAG dependencies preserved. The identical replacement API remains available through migrated transitive imports on restoration; no edit is needed here. |
| Sheaf.CategoryTheory.CartanEilenbergComparisonIndependence | unclaimed | Quarantined archive and all DAG dependencies preserved. The identical replacement API remains available through migrated transitive imports on restoration; no edit is needed here. |
| Sheaf.EtaleCohomology.KunnethOneProper | unclaimed | Quarantined archive and all DAG dependencies preserved. The identical replacement API remains available through migrated transitive imports on restoration; no edit is needed here. |
| Sheaf.Paper.CoefficientChangeDualizing | unclaimed | Quarantined archive and all DAG dependencies preserved. The identical replacement API remains available through migrated transitive imports on restoration; no edit is needed here. |
| Sheaf.Paper.CtfHomCoefficientComparison | unclaimed | Quarantined archive and all DAG dependencies preserved. The identical replacement API remains available through migrated transitive imports on restoration; no edit is needed here. |
| Sheaf.Paper.KunBcKunnethCompat | unclaimed | Quarantined archive and all DAG dependencies preserved. The identical replacement API remains available through migrated transitive imports on restoration; no edit is needed here. |
| Sheaf.RingTheory.AlgebraicRelativeDualizingIsomorphism | unclaimed | Quarantined archive and all DAG dependencies preserved. The identical replacement API remains available through migrated transitive imports on restoration; no edit is needed here. |
| Sheaf.Targets.BaseChangeTowardsFields | unclaimed | Quarantined archive and all DAG dependencies preserved. The identical replacement API remains available through migrated transitive imports on restoration; no edit is needed here. |

The repair of returned head 6593810f0e also restores the complete
FilteredPageTwoComparison module and its original node
lem-sp-filtered-page-two-comparison from that head's parent. They are absent from
both the current source and quarantine trees; no rework row or claim exists for
this module. The source differs only in the required import migration. Its
statement, proof dependencies and blueprint route remain unchanged. The old
review metadata is omitted and restoration metadata identifies this packet.
FlatFilteredComplexComparison is now active and its one proof import is migrated.

## Status

landed 20261020T233220-L-907056 2026-10-20 (merge of deliver/S3/Sheaf.CategoryTheory.FiniteFiltrationInduction)

All twelve adapted modules compile cleanly through lcompile.py --all. A separate
single-file probe importing only the replacement reports exactly propext,
Classical.choice and Quot.sound for restrictionSteps, exists_gradedMap_steps,
gradedMapSteps and finite_filtration_induction_steps. Independent delivery review
and the maintainer's global build remain pending.
