## What changed

Proved AlgebraicGeometry.Scheme.proEtaleConstantRingDerivedPullback_composition_coherence in
Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackCoherence with its original signature. The
retained earlier draft was repaired and checked against current sources. Private helpers expose
the existing determined normalization witnesses, identify ordinary comparisons as adjunction
mates, prove direct-image coherence from fibre-product pasting, and descend ordinary coherence
through the exact-derived functor API. No dependency declaration was changed.

Added proof-only imports WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
and WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction. Updated the existing
node's proof, proof_deps and proof_origin to this route, and removed obsolete tool_uses entries.
The unit sk-d-weil has no realized proof steps; the parent still uses this exact coherence result.

The completed item compiles without warnings in 17.0 seconds through lcompile.py.
The two unchanged direct consumers FrobeniusPullbackComparisonCoherence and IteratedWeilCocycle
compile against it in 6.3 and 4.0 seconds, respectively. Import-cycle
checks accept both added proof imports. The final delivery dry run also checks declaration
signatures and imported axioms. Change record:
coord/changes/P5-proetale-derived-coherence-import-pruning.md.

## Proved and sorry left

Closed one of the original one holes:
AlgebraicGeometry.Scheme.proEtaleConstantRingDerivedPullback_composition_coherence
(lem-trf-derived-pullback-coherence).

Holes added: zero. Sorries left in the item and elsewhere in this delivery: zero.
No split-off statements or modules. This is a proof from the existing unique canonical
comparison characterization and the published exactness interfaces; imported unfinished
statements remain the existing downstream work, not holes added by this delivery.

## No longer needed

Removed public imports Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition and
Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap. The canonical coefficient equality used here is
already in ProEtaleConstantRingPullbackComparison (pur713-def-pullback-comparison), so the
separate lem-trf-constant-coefficient-composition and prop-weil-pbc-proetale-constant-ring-map
proof dependencies and their direct tool approval are unnecessary for this proof. Their uses
elsewhere in the library remain unaffected.

Removed proof imports Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback,
Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients,
Sheaf.Paper.KFlatRingedToposPullback,
Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations,
Sheaf.AlgebraicGeometry.ProEtaleInverseImage, and
Sheaf.Paper.IntegralFinitePullbackComposition. The operations and inverse-image interfaces
are already supplied by the retained statement import. The integral finite wrapper is not
used: the existing general canonical comparison supplies precisely the required normalization.

The proof no longer invokes lem-pc-kflat-resolution or
lem-weil-pbc-ringed-pullback-preserves-kflat, and their top-level tool_uses entries are removed.
All module pullbacks here are already exact; their representative factorization holds on every
complex. Uniqueness identifies the specified K-flat-normalized comparison with that exact-derived
comparison. Consequently a new K-flat representative and its naturality cancellation are
unnecessary in this item. These lemmas may remain transitively needed by the existing
characterization theorem; no claim of whole-library module withdrawal is made.

## Where the brief, the DAG or earlier work was wrong

The original route's fresh K-flat resolution and cancellation are unnecessary for the published
exact mapDerivedCategory interface. The existing comparison's uniqueness theorem already
contains the normalization needed to justify the shorter route. The node now records that
argument. The first retained draft was unverified and had expensive concrete comparisons of
functor constructions, instance mismatches, and incomplete sectionwise transport calculations;
these were repaired through generic categorical lemmas with explicit transports and arguments.

Choice is applied only to determined normalization data, not to arbitrary existence witnesses.
The normalized adjunctions have fixed units, d has fixed section maps, a is its unique conjugate,
and b has fixed degree maps. This also covers empty schemes, identity morphisms, the zero ring,
and unbounded derived objects without extra hypotheses. No statement is disputed.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
