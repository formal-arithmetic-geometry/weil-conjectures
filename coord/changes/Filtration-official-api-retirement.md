# CategoryTheory filtered-object API retirement

## Reason

This is the zero-hole `retire-first` repair in coord/retire-items.tsv. The upstream sync
now provides the complete filtration compatibility API in
`WeilConjectures.CategoryTheory.CanonicalFiltration`. Keeping its Sheaf copy introduces
identical constant names from two modules in one environment. coord/rework.tsv records
13 collision roots, including FilteredHomComplexInvariance and FiniteFilteredLocalization.
The assigned module already has zero holes; closing a different theorem is not part of
this retirement.

The only extra data type in the Sheaf copy is HomPreservingSteps, itself an exact duplicate
of upstream FilteredObject.Hom. Use the latter directly. Its hom field and preservation
proposition are identical, since step is an abbreviation of F. Identity, composition,
induced and quotient filtrations, separatedness, exhaustiveness and graded pieces all
use the official category and definitions. Empty, zero, constant and unbounded
filtrations introduce no additional condition; no finiteness assumption is added.
Source: Stacks Project, homology.tex, definition-filtered (Tag 0121), clauses (1)-(9);
current blueprint main-20261015, def-sp-filtration. Its definition of finite and separated
is already upstream DecreasingFiltration.IsFiniteSeparated, which is untouched.

## Old

The withdrawn module publicly imported:
```lean
public import WeilConjectures.CategoryTheory.Filtration
public import WeilConjectures.CategoryTheory.Abelian.Filtration
```
It redeclared step, antitone_step, the FilteredObject category instance, induced,
quotient, HasIntersection, HasUnion, IsSeparated, IsExhaustive and gradedPiece.
Its extra morphism structure was:
```lean
structure HomPreservingSteps (A B : FilteredObject C) where
  hom : A.obj ⟶ B.obj
  preserves : ∀ i : ℤ, ∃ lift : (A.filtration.step i : C) ⟶
    (B.filtration.step i : C),
    lift ≫ (B.filtration.step i).arrow = (A.filtration.step i).arrow ≫ hom
```

## New

All 11 direct active consumers replace the old import with:
```lean
public import WeilConjectures.CategoryTheory.CanonicalFiltration
```
FiniteFilteredColimitModel retains its proof-only import visibility (`import`, without
`public`). All active occurrences of HomPreservingSteps use the existing official type:
```lean
structure Hom (A B : FilteredObject C) where
  hom : A.obj ⟶ B.obj
  preserves : ∀ i : ℤ, ∃ lift : (A.filtration.F i : C) ⟶
    (B.filtration.F i : C),
    lift ≫ (B.filtration.F i).arrow = (A.filtration.F i).arrow ≫ hom
```
The 15 adapted modules are listed in Users. Public theorem/definition signatures
in BoundedBelowCoproductFiltration and FiniteFiltrationInduction, and the hyper-Ext
statement, now refer to the official Hom; this changes the Lean representation, with
exactly the same underlying morphism and preservation predicate. No target statement
is changed. These three modules are unclaimed. The local constructions in
ExactCoupleMorphism, EnoughStrictFilteredInjectives and FiniteRangeComparison use Hom
as well. All original theorem bodies are retained except for these type-name changes.

FiniteRangeComparison and TruncationExchangeAbutment currently contain only private
active declarations (their public statements are commented out in the baseline).
Both therefore already emit the privateModule linter warning on compilation. Set
`linter.privateModule false` locally in those two helper-only files; no declaration,
visibility or mathematical statement changes.

The four delivered DAG attachments update only Lean representation metadata: the three
active signatures containing the old type name and the def-sp-filtration compatibility
note. Their mathematical statements, dependency plans and unit routes stay intact.
No upstream file is edited. Existing upstream signatures, attributes, public imports,
and definition bodies are preserved. Consumers still see DecreasingFiltration,
FilteredObject and the same finite/separated/graded constructions. Target meaning does
not change, so no target statement review is reopened by this representation repair.

## Users

Source-only tools/downstream.py now reports 95 transitive users and five external users of
HomPreservingSteps. ExactCoupleMorphism has two further occurrences in its source and
is also adapted. Every active direct importer is redirected. Quarantined modules are
not restored by this packet; their later restorations use the official API.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.BoundedAboveCoherentRHom | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.Algebra.Homology.BoundedAboveRHomHyperExt | unclaimed | Uses official FilteredObject.Hom in place of the duplicate morphism type; identical fields and mathematical hypotheses. |
| Sheaf.Algebra.Homology.CoherentRHomFiniteInjectiveDimension | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.Algebra.Homology.CompleteLocalCoherentDuality | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.Algebra.Homology.FilteredBoundedLocalizationComparison | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.Algebra.Homology.UniformFiniteFilteredLocalization | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.AlgebraicGeometry.BoundedComplexDirectImagePresheaf | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.AlgebraicGeometry.BoundedContinuityDirectImage | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ClosedPointSupportDetection | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.AlgebraicGeometry.CondensedSubfieldBoundedCopowers | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ConstantFiniteComparison | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.AlgebraicGeometry.EllAdicProperBoundedBelowCoproducts | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Import official CanonicalFiltration instead of the withdrawn module; no mathematical change. |
| Sheaf.AlgebraicGeometry.EtaleOriginOpenRestrictionTransport | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ExceptionalBaseChangeCartesianOpenInjectiveAcyclic | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.AlgebraicGeometry.FiniteRangeComparison | unclaimed | Use official Hom in a proof construction; no statement change. |
| Sheaf.AlgebraicGeometry.ProEtale.HypercoverComplex | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProEtaleAbelianHypercoverAugmentation | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProEtaleAbelianHypercoverQuasiIso | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProEtaleAbelianHypercoverRowComparison | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProEtaleAbelianHypercoverTotal | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProEtaleBoundedBelowCoproducts | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuityDirectImage | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuitySections | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProEtaleHypercoverAugmentation | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProEtaleHypercoverInjectiveComparison | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProEtaleHypercoverInjectiveRow | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProEtaleHypercoverQuasiIso | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProEtaleHypercoverTotal | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProEtaleModuleCohomologyCoproducts | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProperHeartContinuityDirectImage | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.AlgebraicGeometry.TruncationExchangeAbutment | unclaimed | Import official CanonicalFiltration instead of the withdrawn module; no mathematical change. |
| Sheaf.AlgebraicGeometry.UnboundedEtaleCohomologyAcyclicBasis | unclaimed | Import official CanonicalFiltration instead of the withdrawn module; no mathematical change. |
| Sheaf.CategoryTheory.AcyclicCechEdgeCompatibility | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.CategoryTheory.AcyclicCoproductExtOrthogonalHom | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.CategoryTheory.BoundedBelowCoproductFiltration | unclaimed | Uses official FilteredObject.Hom in place of the duplicate morphism type; identical fields and mathematical hypotheses. |
| Sheaf.CategoryTheory.CartanEilenbergComparisonHomotopy | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.CategoryTheory.CartanEilenbergDoubleComplexHomotopy | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.CategoryTheory.CartanEilenbergDoubleComplexHomotopyComponents | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.CategoryTheory.CartanEilenbergDoubleComplexHomotopyFiltration | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.CategoryTheory.CartanEilenbergFunctorial | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.CategoryTheory.CartanEilenbergProperties | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.CategoryTheory.ContinuousCocontinuousDerivedShriek | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.CategoryTheory.DerivedCategory.BoundedBelowSectionModel | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.CategoryTheory.DerivedColimitBar | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.CategoryTheory.DoubleComplexFirstFiltrationDifferential | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.CategoryTheory.DoubleComplexFirstFiltrationMap | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.CategoryTheory.DoubleComplexTotal | unclaimed | Import official CanonicalFiltration instead of the withdrawn module; no mathematical change. |
| Sheaf.CategoryTheory.EnoughStrictFilteredInjectives | unclaimed | Import official CanonicalFiltration instead of the withdrawn module; no mathematical change. |
| Sheaf.CategoryTheory.ExactCoupleMorphism | unclaimed | Use official Hom in a proof construction; no statement change. |
| Sheaf.CategoryTheory.FiniteFilteredColimitComparison | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.CategoryTheory.FiniteFilteredColimitModel | unclaimed | Import official CanonicalFiltration instead of the withdrawn module; no mathematical change. |
| Sheaf.CategoryTheory.FiniteFiltrationInduction | unclaimed | Uses official FilteredObject.Hom in place of the duplicate morphism type; identical fields and mathematical hypotheses. |
| Sheaf.CategoryTheory.FirstQuadrantRowCollapse | unclaimed | Import official CanonicalFiltration instead of the withdrawn module; no mathematical change. |
| Sheaf.CategoryTheory.GoodTruncationTotalBoundaryImage | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.CategoryTheory.GoodTruncationTotalImage | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.CategoryTheory.GrothendieckCanonicalImageFiltration | unclaimed | Import official CanonicalFiltration instead of the withdrawn module; no mathematical change. |
| Sheaf.CategoryTheory.InjectiveGradedFiltrationSplits | unclaimed | Import replacement only; preserve V3's newly landed complete proof and private helpers. |
| Sheaf.CategoryTheory.InjectiveTargetHomSymbol | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.CategoryTheory.RingedSiteCechRefinementSquare | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.CategoryTheory.SiteAugmentationSpectralSequence | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.CategoryTheory.SiteCechEdgeNormalization | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.CategoryTheory.SpectralSequenceComparison | unclaimed | Import official CanonicalFiltration instead of the withdrawn module; no mathematical change. |
| Sheaf.Paper.CondensedHypercoverComparison | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.Paper.CondensedHypercoverInjectiveRow | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.Paper.CondensedQcqsPushforwardContinuity | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.Paper.CondensedQcqsPushforwardLocalComparison | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.Paper.CondensedUnderivedPushforwardContinuity | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.Paper.ConstructibleRHomCoproductContinuity | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.Paper.EtaleLocalMonodromyRealization | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.Paper.FiniteFilteredGradedExactness | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.Paper.FiniteHorizontalShriekComposition | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.RingTheory.CotangentBootstrap | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.RingTheory.CotangentTransitivityTriangle | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.RingTheory.EtaleCotangentVanishing | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic | unclaimed | Same filtration notions and operations from official CanonicalFiltration; no source adaptation required. |
| Sheaf.AlgebraicGeometry.CartesianOpenFiniteStageHypercohomologyModel | unclaimed | No filtration API occurrence in active code; its transitive dependency uses the official replacement. No source adaptation required. |
| Sheaf.AlgebraicGeometry.EllAdicProperConstructibleCohomology | unclaimed | No filtration API occurrence in active code; its transitive dependency uses the official replacement. No source adaptation required. |
| Sheaf.AlgebraicGeometry.EllAdicProperHeartUniformBound | unclaimed | No filtration API occurrence in active code; its transitive dependency uses the official replacement. No source adaptation required. |
| Sheaf.Paper.EtaleLocalMonodromyRealizationBase | unclaimed | No filtration API occurrence in active code; its transitive dependency uses the official replacement. No source adaptation required. |
| Sheaf.Paper.NormalizedMonodromyFunctor | unclaimed | No filtration API occurrence in active code; its transitive dependency uses the official replacement. No source adaptation required. |
| Sheaf.SixFunctors.AdmissibleDirectImage | unclaimed | Not affected: the textual IsSeparated hits are AlgebraicGeometry.IsSeparated on the scheme morphisms X to Spec k, Y to Spec k, and f (lines 92, 94, 96), not DecreasingFiltration.IsSeparated. No filtration declaration or direct import of the retired module occurs; no source adaptation required. |

| Sheaf.AlgebraicGeometry.CoherentEtaleComparisonPullback | unclaimed | No filtration API occurrence in active code; its transitive dependency uses the official replacement. No source adaptation required. |
| Sheaf.AlgebraicGeometry.CoherentPowerComparison | unclaimed | No filtration API occurrence in active code; its transitive dependency uses the official replacement. No source adaptation required. |
| Sheaf.AlgebraicGeometry.QcoherentNormalizedComparison | B2 | Not affected: its IsSeparated occurrence (line 97) is Scheme.IsSeparated X, not CategoryTheory.DecreasingFiltration.IsSeparated. The transitive DoubleComplexTotal import uses the official replacement; no source adaptation required. |
| Sheaf.AlgebraicGeometry.QcoherentNormalizedPullbackSquare | B3 | Not affected: its two IsSeparated occurrences (lines 85-86) are Scheme.IsSeparated X and Scheme.IsSeparated Y, not CategoryTheory.DecreasingFiltration.IsSeparated. The transitive DoubleComplexTotal import uses the official replacement; no source adaptation required. |
| Sheaf.CategoryTheory.EdgeCollapse | unclaimed | S9 landed a complete proof during repair preflight and independently removed the retired import. Current source has no filtration API dependency needing adaptation; the stale sandbox copy was removed, preserving the landed proof and private helpers. |
| Sheaf.Paper.CondensedFiniteFreeHomEvaluation | unclaimed | No filtration API occurrence in active code; its transitive dependency uses the official replacement. No source adaptation required. |
| Sheaf.Paper.CondensedInternalHomSections | unclaimed | No filtration API occurrence in active code; its transitive dependency uses the official replacement. No source adaptation required. |

## Status

landed 20261020T161325-L-3477155 2026-10-20 (merge of deliver/X3/Sheaf.CategoryTheory.Filtration)

The retained packet compiled all 16 consumer modules on 2026-10-20. During that
verification V3 landed a proof of injective_graded_filtration_splits. The sandbox
consumer was refreshed from the current source, preserving its proof and private
helpers verbatim and replacing only the retired public import. The consumer is now
unclaimed. The refreshed consumer compiled cleanly through lcompile.py (2.9 s).
All 16 sandbox modules compiled, and deliver3.py --no-push passed preflight
(commit 36da553132d, CODEX review class). Independent review and the maintainer
global build remain pending.

Return repair (head 83a79e7c6): added the missing AdmissibleDirectImage user and
explained its unrelated scheme-morphism IsSeparated occurrences. Refreshed the
source-only downstream scan and added its other five new transitive users. All
16 retained Lean files were compared against the current source: the only
differences are the intended migration and existing local linter settings; the
newly landed complete InjectiveGradedFiltrationSplits proof remains intact.

Repair validation: all 16 sandbox modules compile through lcompile.py --all;
deliver3.py --no-push passed (8f673eb02c5, CODEX review class). Refreshed
the three released user claims to unclaimed. Independent review and the global
build remain pending; the change record therefore stays open.

Return repair (head 36e974bf1): added the two missing QcoherentNormalized users.
Their Scheme.IsSeparated class assumptions concern schemes and are unrelated to
filtration separatedness; no changes to those modules are necessary. Added the
other new transitive users from the fresh scan. A concurrent S9 landing proved
EdgeCollapse and removed its retired import during the first dry run. Preflight
correctly rejected the stale adaptation; the sandbox copy was removed, leaving
the complete current proof and all private helpers untouched. The 16 previously
retained consumer files were compared against current sheaf-dag sources; all
newer proofs remain intact. No new holes or mathematical changes are introduced.

Repair validation: lcompile.py --all compiled all 16 retained consumer modules
successfully after dropping the stale EdgeCollapse adaptation. No new holes.

The repaired packet passed deliver3.py --no-push at 7db8e1fe2e
(CODEX review class). Independent review and the global build remain pending.
