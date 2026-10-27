## What changed

Reduced ambientProperOpenPasting to two independent remaining mathematical results,
with complete ordinary tensor and canonical system Laws proofs in the parent. The
shared Calculus definitions moved verbatim to AmbientProperOpenCalculus, publicly
re-exported at the original module. Added the proved generic pro-etale derived tensor
composition theorem and two proved presentation/representative uniqueness interfaces.

Private equality specifications retain the already constructed native mates during
component conversion. Their witnesses, uniqueness and identifying equations are fully
proved. These proof helpers leave all public operation definitions unchanged.

The shared-interface relocation is necessary to state the ordinary and tensor clauses
without importing the theorem which consumes them; it does not change an operation or
serve as a compile-time partition. The parent proof uses private component lemmas and
explicit operation and compositor equalities to avoid repeatedly unfolding derived
functor records.

Validation: all seven packet modules and twelve unchanged current consumers compiled
successfully through ordered lcompile checks. No consumer adaptation was needed. The
original theorem signature is byte-identical to the shared source; the relocated
operation definitions remain verbatim, with only blueprint references updated.

## Proved and sorry left

Closed: AlgebraicGeometry.ProEtale.AmbientProperOpen.ambientProperOpenPasting (one original
hole), by decomposition. Added two holes:
AlgebraicGeometry.ProEtale.AmbientProperOpen.ordinaryAmbientProperOpenLaws
(lem-sf-ordinary-ambient-proper-open-laws), and
AlgebraicGeometry.ProEtale.AmbientProperOpen.publishedSystemTensorComposition
(lem-sf-published-system-tensor-composition).
This is a decomposition: one packet hole closed and two added. No axiom-free proof gain
is claimed.
The ordinary tensor clause and all twelve canonical system Laws clauses have complete
Lean proof terms; delivery compilation validates the assembly. The generic tensor
compositor, the six system presentation/compositor identifications, and
tensorComparison_unique_on_flat_representatives have no sorry.

## No longer needed

The parent uses native semilinearProperOpenMatePasting instead of reproving system
clopen pasting or detecting equality through derived evaluation. The ordinary geometric
clopen argument remains needed in its separate ordinary-laws result. The ambient
pullback tensor theorem remains needed for the published-system normalization result.
The removed private imports of the original module are:
WeilConjectures.CategoryTheory.SiteMorphismComposition;
Sheaf.AlgebraicGeometry.ProEtaleTensorCompositionUnit;
Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition;
Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization;
Sheaf.CategoryTheory.SiteInverseImageTensor; Sheaf.Paper.FiniteClopenDerivedDecomposition;
Sheaf.CategoryTheory.LocalizedModuleExactForSystems;
Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations;
Mathlib.CategoryTheory.Localization.Adjunction;
Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses;
Sheaf.Paper.SemilinearDerivedSections; Sheaf.SixFunctors.OpenTensorNormalization;
WeilConjectures.Compactification.Refinement.
Their needed interfaces remain public dependencies of the shared calculus or explicit
proof dependencies of the new clauses; no whole module is claimed pruned.
The generic tensor-composition module also removes unused imports of
UpperStarCompCoherence, Monoidal.Conjugate, Sites.PushforwardMonoidal,
and RingSheaf.UpperStarSquare. FlatModuleCat is needed only
for the parent’s ordinary coefficient specialization and is imported privately there.
The parent also drops private access to StrictTowerDirectImageCoherence,
VaryingRingProperOpenPasting and SemilinearProperOpenMatePasting. The first two
node dependencies (lem-cbc-strict-tower-direct-image-coherence and
lem-sp-varying-ring-proper-open-pasting) are unnecessary for its generic mate
calculations: the public mate API and direct conjugation proofs suffice. Their
modules may remain needed through other routes. The ordinary semilinear import stays.
No source-library declaration is removed. No unit statement or realized step is bypassed.
The original unit retains its
ordinary tensor, ordinary clopen and simultaneous-system assertions. No whole DAG node
or module is withdrawn: all former geometric dependencies remain on the ordinary-laws
route, and the system tensor route retains ambientPullbackTensorCoherence.
The shared interface module drops all former private proof imports; the parent imports
only the adjunction/mate interfaces and the ordinary derived tensor proof it uses.

## Where the brief, the DAG or earlier work was wrong

The proposed assembly is not a direct specialization of AmbientCompositor.Operations:
its Hom universes differ from the ordinary total-derived pro-etale realization. The
ordinary calculus uses total left-derived upperStar, while the exact-localization
certificate uses mapDerivedCategory, so transport and compositor normalization are
substantive. The ambient system tensor comparison and the published comparison have
different defining representative rectangles; their identification is a separate
normalization argument, not definitional equality. No false statement was found.

## New nodes

- def-sf-ambient-proper-open-calculus: verbatim relocation of the shared interface.
- lem-sf-ordinary-ambient-proper-open-laws: ordinary geometric coherence clause.
- lem-sf-published-system-tensor-composition: published system tensor normalization.
- lem-sf-proetale-derived-pullback-tensor-composition: proved generic derived tensor law.
- lem-sf-system-pullback-compositor-identification: proved presentation uniqueness.
- lem-sf-system-pullback-tensor-normalization: proved representative uniqueness.

Change record: coord/changes/H4-ambient-proper-open-calculus.md.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
