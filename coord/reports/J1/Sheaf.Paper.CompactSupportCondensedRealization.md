## What changed

Closed four original proof holes in Sheaf.Paper.CompactSupportCondensedRealization:
sectionFieldMap_existsUnique reuses the existing reconstructed section-ring map and
proves uniqueness by sectionwise extensionality; encodingScalarMap_isIso applies the
inverse-mate theorem for the existing derived encoding equivalences; fieldScalar_preserves
and omegaScalar_preserves apply the general bounded-constructible exact-scalar theorem.
All public declaration signatures, definition bodies and exported attributes remain
unchanged. Local coefficient instances and a local derived-category reducibility barrier
avoid unnecessary expansion during elaboration. Removed unused direct private imports.

After profiling and local optimization still left the module over the 60-second limit,
moved its self-contained prefix (48 public declarations through latticeScalar) into
Sheaf.Paper.CompactSupportCondensedRealizationSetup. The item publicly re-exports it;
all original public imports remain. The six original unfinished declarations in that
prefix keep their names, statements, bodies and complete proof docstrings. This is a
module separation, not a decomposition into new mathematical obligations. The new setup
node records those declarations, and the original node depends on it. No new sorry
statement is introduced. A source comparison after recombining the files verifies that
every original declaration, definition body, attribute and statement option is unchanged
apart from the four filled theorem proofs and docstrings. The change record is
coord/changes/compact-support-condensed-realization-setup.md.

Both finalized modules passed standalone remote compiles; the main file took 36.5 seconds.
All 17 current direct importers passed remote compilation against these sandbox modules.
After the factor-normalization coordinate separation, all five of that module's direct
importers passed remote compilation again.
Unchanged consumer copies and diagnostic sources were removed from the packet.

The unclaimed direct importer Sheaf.Paper.CompactSupportRealizationFactorNormalization
also exceeded the limit on the unchanged baseline (70.8 seconds). Its compilation repair
adds local unfolding barriers, synchronous elaboration, and enables respecting
transparency separately for declarations compatible with that setting. Its original
global settings are retained for the other six declarations; no option disabling
transparency is added. The first repaired version passed a standalone compile in 34.0 seconds, but the
delivery compile took 65 seconds and was rejected. Profiling showed distributed typeclass
and kernel-checking cost; local priority for existing category instances did not improve
it. After these optimization attempts, separated the self-contained prefix (32 public
declarations through systemPresentation) into Sheaf.Paper.CompactSupportRealizationCoordinates.
The original importer publicly re-exports it and retains every original public import.
Both separated files passed remote compilation.
Recombining the sources, ignoring comments, reproduces every declaration, definition body,
proof and exported attribute byte for byte apart from whitespace and the documented local
elaboration commands. Its 12 original holes are unchanged; three move with the prefix.
The existing coordinate-definition node is attached to the new implementation module;
the new setup node records the original prefix and its auxiliary obligations.

Reviewer correction (2026-10-27): the private `import all
Sheaf.Paper.CondensedCompactSupportProjection` the delivery added to the unclaimed
importers CondensedOpenCounitUnits and CondensedOpenCounitRealization is withdrawn. Their
unchanged originals compile against the delivered modules (40.7 s and 6.1 s), so the
adaptation was not forced; both modules stay as published.

## Proved and sorry left

Original holes: 17. Closed: 4. Added: 0. No decomposition.
All names below, except the final theorem, are in the namespace
WeilConjectures.CompactSupportCondensedRealization.

Closed:

- sectionFieldMap_existsUnique
- encodingScalarMap_isIso
- fieldScalar_preserves
- omegaScalar_preserves

Remaining original holes (13). Six now live in the setup module, attached to
lem-pur-compact-support-condensed-realization-setup:

- fieldExtension_flat
- omegaExtension_flat
- scalarModelTransport_subsingleton
- scalarModelTransport_nonempty
- realizedCoefficient_square
- encodingRestriction_existsUnique

Seven remain in the item, attached to lem-pur-compact-support-condensed-realization:

- finiteProjection_isIso
- omegaProjection_isIso
- omegaSupport_preserves
- systemRefinement_id
- systemRefinement_comp
- omegaRefinement_isIso
- compactSupport_condensedRealization


The adapted importer's original holes are unchanged; these are not added obligations.
All are in namespace WeilConjectures.CompactSupportFactorNormalization. The first three
now live in CompactSupportRealizationCoordinates with node
lem-zl-compact-support-realization-coordinates-setup:

- integralComparison_normalization
- ordinaryRestrictionSquare_existsUnique
- ordinaryRestrict_kInjective

Nine remain in CompactSupportRealizationFactorNormalization, with the original node
lem-zl-compact-support-realization-factor-normalization:

- realization_factor_normalization
- coefficient_open_unit
- coefficient_proper_isIso
- integral_naturality
- single_realization
- realization_identity_open
- coefficient_identity_open
- factorization_naturality
- completed_bridge

## No longer needed

Removed the following direct private proof imports. The delivered partial proofs use
neither their geometric comparison assertions nor their reconstruction existence
statements. Any interfaces still needed by existing definitions remain available through
the unchanged public imports. No module is withdrawn, and no original dependency node
is declared globally obsolete: the unreduced reconstruction, projection and refinement
holes retain their original proof plan.

- Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
- Sheaf.Paper.AdicCoefficientDatum
- Sheaf.Paper.IntegralUniformCoefficient
- Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
- Sheaf.Paper.ExactProductFunctorStrictLimit
- Sheaf.Paper.IntegralCompactSupportUniformRestriction
- Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
- Sheaf.Paper.RingedCoefficientProjectionCocycle
- Sheaf.SixFunctors.OpenTensorNormalization
- Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
- Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
- Sheaf.AlgebraicGeometry.FiniteFreeDirectImageCoherence
- Sheaf.CategoryTheory.StrictTowerArithmeticRestriction
- Sheaf.Paper.FiniteFreeCompletedScalarComparison
- Sheaf.AlgebraicGeometry.CondensedCoefficientComplexPresentation
- Sheaf.Paper.CondensedFlatCoefficientCalculus
- Sheaf.Paper.CondensedQcqsPushforwardContinuity
- Sheaf.Paper.ConstantCompletionEquivalence
- Sheaf.Paper.ContinuousCoefficientRealizations
- Sheaf.Paper.DerivedAdjunctionShift
- Sheaf.CategoryTheory.DiagramSiteRealization
- Sheaf.Paper.IntegralStratifiedPerfectCharacterization
- Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
- Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
- Sheaf.Paper.ProjectionMateExact
- Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
- Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect
- Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
- Sheaf.Paper.CompletedDirectImageLimits
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
- Sheaf.Paper.PbcRationalTransport

## Where the brief, the DAG or earlier work was wrong

The general exact-scalar constructibility theorem already handles arbitrary coefficient
embeddings once flatness is supplied. The encoding scalar mate needs only the existing
encoding equivalences and the normalized restriction isomorphism; it does not require
rebuilding balanced tensor inverses. The original unmodified module took 74.2 seconds
on its baseline remote compile. After profiling and local elaboration work the complete
monolithic proof file still took at least 67.1 seconds, so the self-contained setup was
separated under the brief's compile-time splitting rule. The rework row was checked;
the current source is present. The original mathematical declarations and dependencies
are preserved, with the moved declarations attached to the new setup node.

## New nodes

lem-pur-compact-support-condensed-realization-setup records the original prefix through
latticeScalar in its new implementation module. It introduces no new public mathematical declaration,
signature or proof obligation. Its six existing unfinished theorems retain their original
sources and proof plans; sectionFieldMap_existsUnique and encodingScalarMap_isIso are
proved there. The record's proof describes the same tower, scalar and section-encoding
constructions as the original module. No matching separate setup assertion was found in
the current blueprint, and the unit route is preserved.

lem-zl-compact-support-realization-coordinates-setup records the original factor-normalization
coordinate prefix through systemPresentation, separated only for compilation. All 32 public
declarations and their three existing unfinished theorems are unchanged. The existing
def-pur-compact-support-realization-coordinates node retains its statement and is attached
to the new module. The factor-normalization theorem node uses the setup and retains the
remaining normalization plan. No mathematical statement or proof obligation is added.

Change record: coord/changes/compact-support-condensed-realization-setup.md.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
