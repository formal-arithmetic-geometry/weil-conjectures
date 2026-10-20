## What changed

Repaired the quarantined Sheaf.AlgebraicGeometry.QCohTensorResolutionChartComparisonIso
by re-exporting its complete source-library counterpart. The specified chart
augmentation, restricted resolutions and four-map common-resolution comparison
are preserved. This replaces the broken duplicate-declaration import route;
it is neither a withdrawal nor a no-op restoration.

Restored the complete archived downstream component in the same packet:
QCohTensorResolutionChartComparisonIsoFormula,
QCohTensorResolutionChartComparisonNaturality,
QCohTensorResolutionCoordinateChartIso,
QCohTensorResolutionCoordinateSheafIso,
QCohTensorResolutionCoordinateFactorization,
QCohTensorResolutionCoordinateSections,
QCohTensorResolutionCoordinateSectionsNaturality and
QCohOrdinaryTensorResolutionCoordinates (all under Sheaf.AlgebraicGeometry).

Seven consumer modules re-export complete source-library counterparts.
The separate tensorResolutionCoordinateChartIso helper is retained, with
canonical imports and the equivalent IsKFlatTensor predicate. To avoid a
60-second timeout elaborating the original direct composite, construct it by
normalizing the canonical full-coordinate isomorphism. Its final inverse
normalization cancels, giving the same original chart comparison. The helper
compiles in 42.7 seconds without increasing the file timeout. All eight
consumer modules were unclaimed. No file under lean/WeilConjectures is changed.
The source and legacy K-flat predicates have verbatim identical bodies,
differing only in their public names.

Reattached five existing DAG lean records to their canonical source declarations:
new-h4-qcoh-chart-comparison-hom-identification,
new-t3-qcoh-tensor-resolution-chart-comparison-naturality,
new-t3-qcoh-tensor-resolution-coordinate-factorization,
new-g2-existing-qcoh-tensor-resolution-coordinate-naturality and
new-j1-qcoh-ordinary-tensor-resolution-coordinates.
Their mathematical statements and dependency plans stay unchanged.
No DAG node was attached to the item module itself.

Change record: coord/changes/C1-qcoh-chart-comparison-canonical.md.

## Proved and sorry left

The assigned preserved definition tensorResolutionChartComparisonIso has zero
sorries. This is a zero-hole definition/import repair: 0 holes closed,
0 holes added, 0 split off, 0 remaining in the delivered modules. No theorem
is claimed as newly proved by this session.

The canonical tensorResolutionChartComparisonIso has a complete construction;
its axiom check reports only propext, Classical.choice and Quot.sound.
The archived defining-formula consumer, with only the equivalent canonical
K-flat spelling substituted, compiles by rfl against the repaired module.

All nine restored modules compile; a combined API check imports them together
and checks all nine main declaration names and their axioms. Every checked
declaration uses only the three permitted axioms. A Lean cancellation check
proves that composing the retained chart helper with inverse normalization
recovers tensorResolutionCoordinateSheafIso, using only Iso.trans_assoc,
Iso.self_symm_id and Iso.trans_refl. The source factorization formula identifies
this uniquely with the original direct chart composite. All exploratory checks
live under scratchpad, outside the delivery's Lean files.

## No longer needed

The old duplicate Sheaf implementation of tensorResolutionChartComparisonIso
and seven duplicate consumer implementations are replaced by public re-exports
of their complete canonical declarations. Their module paths remain available.
No module or DAG node is withdrawn. No dependency is declared globally unused:
the source implementations retain the same mathematical proof route and
upstream declarations and imports remain untouched.

Removed direct imports from the restored archived component (canonical public
imports supply the needed interfaces):

- import Sheaf.Algebra.Homology.KFlatResolution
- import Sheaf.AlgebraicGeometry.QCohTensorResolutionChartAugmentationNaturality
- import Sheaf.AlgebraicGeometry.QCohTensorResolutionChartComparisonIsoFormula
- import Sheaf.AlgebraicGeometry.QCohTensorResolutionChartComparisonNaturality
- import Sheaf.AlgebraicGeometry.QCohTensorResolutionChartHomologyNaturality
- import Sheaf.AlgebraicGeometry.QCohTensorResolutionComparisonRestrictionNaturality
- import Sheaf.AlgebraicGeometry.QCohTensorResolutionCoordinateFactorization
- import Sheaf.AlgebraicGeometry.QCohTensorResolutionCoordinateSectionsNaturality
- import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionSectionNaturality
- public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
- public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
- public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
- public import Mathlib.AlgebraicGeometry.Modules.Sheaf
- public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
- public import Sheaf.Algebra.Homology.KFlat
- public import Sheaf.AlgebraicGeometry.QCohTensorResolutionChartComparisonIso
- public import Sheaf.AlgebraicGeometry.QCohTensorResolutionChartComparisonIsoFormula
- public import Sheaf.AlgebraicGeometry.QCohTensorResolutionChartModel
- public import Sheaf.AlgebraicGeometry.QCohTensorResolutionComparison
- public import Sheaf.AlgebraicGeometry.QCohTensorResolutionCoordinateChartIso
- public import Sheaf.AlgebraicGeometry.QCohTensorResolutionCoordinateSections
- public import Sheaf.AlgebraicGeometry.QCohTensorResolutionCoordinateSheafIso
- public import Sheaf.AlgebraicGeometry.QCohTensorResolutionHomologyCoherence
- public import Sheaf.AlgebraicGeometry.QCohTensorResolutionKFlatBundledRing
- public import Sheaf.Paper.DerivedHomMayerVietoris

No unit route is bypassed. The quarantined archives and all five node
attachments are preserved, with the latter relocated to canonical declarations.

## Where the brief, the DAG or earlier work was wrong

The item is a quarantined zero-hole definition repair, rather than an open
proof obligation. coord/rework.tsv records the duplicate isKFlat_tilde error;
the preserved source is in quarantine, not lean/.

The synced source library already supplies the complete construction and all
seven migrated consumer counterparts. Reintroducing the archived declarations
would duplicate their names. Merely re-exporting the comparison without adapting
its archived consumers would leave unknown IsAcyclicTensorKFlat identifiers;
the full affected component is therefore migrated together. The standalone
chart-coordinate helper has no canonical source declaration and is retained.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
