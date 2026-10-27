## What changed

Restored the quarantined item and replaced its single proof hole by an assembly
proof. The original ComparisonSpec and theorem signatures are unchanged. The
assembly chooses one family of normalized scalar section models and uses that
same family for every tensor and pullback comparison.

Moved the fixed definitions, verbatim except their blueprint tags, into the new
public prerequisite Sheaf.Paper.QuotientSectionTensorData. The parent publicly
imports it, retaining its original public import closure. This prevents cycles
between the definitions and the independent proof steps. The change record is
coord/changes/T3-quotient-section-tensor-data.md. No source-library file changes. The first delivery preflight found two
DAG signature strings containing an attribute or definition body; both records
were corrected to the parser's signature format. No Lean change was needed.

The scalar tensor canonical module constructs the canonical derived tensorator
and proves its cochain normalization. The separate uniqueness module uses
flat-term K-flat resolutions.
The generic scalar calculations are private proof helpers reproduced from the
existing downstream projection-comparison proof; importing that consumer would
create a cycle. The canonical construction and uniqueness have separate modules
after profiling revealed excessive elaboration of their combined instance arguments.

The derived-oplax and tensor-identification modules expose the generic structure
and its defining equations. They were separated after profiling identified
large kernel-checking costs in the combined unit module. The regular-unit module identifies the specified unit with the generic derived
monoidal unit and proves the constraint equations. The geometric module compares
the actual native pullback tensorator with the generic one using the existing
proved upstream-extra identification, then applies the
existing section tensor and pushpull normalization theorems.

Three independent section comparison steps remain as named public theorems in
separate modules. Each records its source, complete proof in words, edge cases,
and DAG attachment. None repeats the parent ComparisonSpec: they concern,
respectively, scalar models, a tensor square, and a scalar/pullback square.

The three unfinished section statements compile (34.4 s, 34.5 s and 32.4 s).
A profiler run of the unchanged data block compiled in 33.7 s; it showed no
individual bottleneck (8.9 s elaboration, 12.3 s checking and 9.5 s linting).
Profiling options have been removed. The geometric normalization proof compiles
in 11.1 s. The scalar uniqueness module compiles in 54.3 s.
The derived-oplax and tensor-identification modules compile in 50.5 s and 47.2 s.
The parent assembly compiles in 47.4 s. The optimized unit proof compiles in 13.9 s after replacing the broad rewrite
by substitution and using two local tensor-map equations. Both direct consumers, QuotientPullbackTensorFlatModel and
QuotientPullbackTensorCoherence, compile unchanged against the delivery. Their
temporary copies have been removed. The compatibility batch reported wall times
91.3 s (data), 70.4 s (unit), 60.2 s (parent), 71.0 s (flat model) and 117.0 s
(coherence), substantially above the isolated profiling runs; delivery preflight
checks the final packet against its own time limit. The scalar tensorator is
marked irreducible to avoid repeated expansion of its large instance arguments;
its normalization theorem exposes the computation square used downstream.

## Proved and sorry left

The original hole in
AlgebraicGeometry.ProEtale.QuotientSectionTensor.quotient_section_tensor_normalization
is closed by a complete assembly proof. This is a decomposition, not a claim that
the original mathematics is completely proved: one original hole is replaced by
three smaller holes (net two additional holes).

The proved new declarations are canonicalTensor_normalized, scalar_compute_isIso,
normalized_tensor_eq_canonical, scalar_tensor_exists_unique,
scalar_regular_unit_isIso, scalarDerivedOplax_δ, scalarDerivedOplax_η,
scalarDerivedOplax_η_isIso, scalar_unit_constraints and geometric_normalization, in the same namespace.
The constructors uncurryTensorIso, canonicalTensor and scalarDerivedOplax, and the named existing-instance
caches scalarSheafSymmetric, scalarModuleClosed, scalarModuleBraided, scalarModuleFlat
and scalarPreservesKFlat, contain no holes.

Exactly three new proof holes remain:

- AlgebraicGeometry.ProEtale.QuotientSectionTensor.scalar_section_exists,
  node lem-sfb-quotient-scalar-section-existence.
- AlgebraicGeometry.ProEtale.QuotientSectionTensor.section_tensor_transport,
  node lem-sfb-quotient-section-tensor-transport.
- AlgebraicGeometry.ProEtale.QuotientSectionTensor.section_pull_transport,
  node lem-sfb-quotient-section-pull-transport.

There are no holes in definitions and no new axioms. The original item has zero
remaining sorry bodies; all three unfinished statements are separate modules.

## No longer needed

Removed these private imports from the original item:
Sheaf.CategoryTheory.InternalSectionTensorComparison,
Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients,
Sheaf.Algebra.Homology.KFlatTotalTensorModel,
Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients,
Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses,
Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses,
Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients.
The parent now imports the narrower proof-step modules instead. Redundant private
imports in the new proof modules were also removed where another prerequisite
already publicly exports the same module.

Their mathematical dependencies are retained where needed by the section
transport nodes. The original proof dependency
lem-sfb-integral-quotient-direct-image-comparison is not used: the generic derived
monoidal construction supplies the scalar tensorator without its direct-image
assertion. Its module Sheaf.Paper.IntegralQuotientDirectImageComparison remains a
public prerequisite for the fixed QuotientChange data and the original public
import closure. No existing node or module is withdrawn or claimed globally
unnecessary. The parent keeps its original statement dependencies and the unit
route. Its proof dependencies now name the six actual assembly steps. The generic
derived-monoidal API supplies the scalar tensor and unit proofs directly, so no
new separate scalar associativity or uniqueness holes are needed.

## Where the brief, the DAG or earlier work was wrong

The assigned source was initially quarantined, not withdrawn. It has been restored
and its definitions and statement preserved. The current shared repository later
restored the file too; the delivery does not delete any quarantine archive.

The planned change-of-rings dependency's attached theorem is about ordinary
rings, while this statement needs sheaves of section rings and a fixed universal
cochain model. The available DerivedChangeOfRingsCochainModel provides the correct
interface; the scalar-section step explicitly records the remaining transport to
that interface rather than applying an ordinary-ring theorem with mismatched data.

SectionDerivedTensorNormalization concerns the generic internalDelta, whereas
GeometricCondition names the native leftDerivedUpperStarTensor. The geometric
proof explicitly identifies them by the existing theorem derived from the
bifunctor-derived universal property.
The preexisting internal scalar/pullback comparison also does not by itself give
the stronger all-complex scalar-section counit normalization recorded here.

Edge cases were checked before stating the splits: empty schemes, zero modules,
zero quotient rings and nonflat coefficient quotients add no assumptions; the
maps are sheafified balancing maps and the derivation uses K-flat resolutions.

## New nodes

- def-sfb-quotient-section-tensor-data: the unchanged fixed normalization data,
  relocated to QuotientSectionTensorData to avoid cyclic imports.
- lem-sfb-quotient-scalar-tensor-canonical: construction and normalization of the
  canonical tensorator, separated after profiling to keep file times bounded.
- lem-sfb-quotient-scalar-tensor-exists-unique: explicit canonical tensorator,
  computation and uniqueness on flat-term K-flat representatives.
- def-sfb-quotient-scalar-derived-oplax: the generic scalar oplax structure and
  its identified, invertible unit.
- lem-sfb-quotient-scalar-derived-tensor-identification: identification of that
  structure's tensorator with canonicalTensor.
- lem-sfb-quotient-scalar-unit-constraints: regular units and monoidal constraints.
- lem-sfb-quotient-scalar-section-existence: scalar generator and universal
  localization normalization for one scheme; unfinished.
- lem-sfb-quotient-section-tensor-transport: section tensor square and its
  generator normalization for given normalized models; unfinished.
- lem-sfb-quotient-section-pull-transport: section scalar/pullback square and its
  ordinary balancing normalization for two given normalized models; unfinished.
- lem-sfb-quotient-geometric-normalization: native pullback tensorator and actual
  adjunction comparisons.

Change record: coord/changes/T3-quotient-section-tensor-data.md.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
