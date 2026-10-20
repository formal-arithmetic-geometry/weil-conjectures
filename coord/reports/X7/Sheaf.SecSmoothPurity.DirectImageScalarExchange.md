## What changed

Proved the direct-image scalar exchange by a coefficient/pullback cube and a generic
mate-counit calculation. The original theorem signature is unchanged.

Added three proved mathematical interfaces: arbitrary Cartesian-square tensor
compatibility, localization of the normalized ordinary pullback compositor, and the
canonical constant-coefficient pullback cube. Their private helpers adapt the existing
ordinary restriction and exact-localization calculations to arbitrary squares; no
open-immersion assumptions are introduced.

Moved the five canonical supporting constructors into DirectImageScalarOperations,
publicly re-exported by the item. The shared directImageConstantPullbackIso factors
exactly the original ambient comparison. An explicitly typed canonical-adjunction
wrapper preserves the original adjunction data while avoiding expensive conversions.
The change record is
coord/changes/direct-image-scalar-operations.md. No source-library file changes.

Repair of returned head 44557e8d5de (reviewer C-44557): the mathematics was accepted;
landing failed while reading the absent, quarantined StrictLocalMateContinuityPresentation
module. The retained packet was compared with the returned head and current sheaf-dag
6428328058d. Its five Lean files are unchanged from the reviewed proof. All five were
recompiled successfully on the project server against the current published build
(7.1, 3.0, 19.0, 5.3 and 4.0 seconds). Delivery rebuilds the commit on current sheaf-dag;
no quarantined module is withdrawn or replaced by this repair.

## Proved and sorry left

Closed 1 of 1 original holes; added 0 holes; split off 0 unfinished statements.
The original hole is AlgebraicGeometry.ProEtale.directImageScalarExchange
(lem-fix-direct-image-scalar-exchange). It is replaced by a complete proof from the
stated canonical operations and the three new proved interfaces. No holes are split
off or added. The new public theorems are:

- AlgebraicGeometry.ProEtale.DirectScalar.scalarTensorPullbackSquare.
- AlgebraicGeometry.Scheme.proEtaleCanonicalDerivedPullback_normalization.
- AlgebraicGeometry.Scheme.proEtaleConstantScalarPullback_cube.

The delivery contains zero occurrences of sorry. The proof still depends on the
existing canonical-composition and scalar-operation interfaces, whose unfinished
proofs remain separate project items.

## No longer needed

The item keeps its original public imports to preserve its exports for 468
transitive importers. The operations module provides the actual constant-ring,
scalar, FourCorners and ambient constructions. The proof adds a private import
of the proved canonical scalar cube.

Removed private imports of KFlatResolutionIndependentCoefficients,
DerivedChangeOfRingsCochainModel, CondensedAmbientExchange and
IntegralFinitePullbackComposition. ProEtaleCanonicalPullbackComposition moves
inside the normalization proof, where it remains needed. No public export or
existing declaration is withdrawn.

The original direct proof dependencies lem-pc-kflat-resolution,
lem-pur-derived-change-of-rings,
lem-weil-pbc-ringed-topoi-derived-tensor-pullback and
lem-weil-pbc-proetale-derived-pullback-composition are replaced at the item level by
the proved cube. The latter composition interface remains needed within its
normalization proof. The retained scalar interfaces also carry their own mathematical
dependencies; none of those declarations or modules is withdrawn. The original
lem-weil-pbc-mate-pasting dependency remains as the generic mates calculus.

The generalized tensor-square proof does not need OpenImmersionSquare or any
open-extension construction. No unit realization is bypassed: the two attached
units have empty realized arrays, and the item and all of its parents remain.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed. The original K-flat generator argument is true, but the
existing exact restriction and localization calculations give a shorter formal route.
The only geometric input to the ordinary restriction-square proof is sq.w, so its
calculation extends from open squares to arbitrary chosen Cartesian squares.

Single-file compilation checks an edit without emitting artifacts for later sandbox
imports. Dependency edits were therefore checked with multi-file compilation, and
all final files were checked together successfully. The seven original constructor
users listed in the change record compiled unchanged against the new artifacts.
Separate rfl checks preserved both the scalar mate and the complete original ambient
exchange. Temporary compilation probes were removed before delivery. Large dependent rewrites in the normalization
proof were replaced by direct congruence, avoiding expensive unfolding of the
canonical data.

## New nodes

lem-sp-canonical-derived-pullback-normalization identifies the actual canonical
derived compositor with the localization of the ordinary compositor conjugate to a
section-normalized direct-image compositor. The proof is complete.

lem-sp-scalar-tensor-pullback-square proves the inverse scalar-comparison cube for
arbitrary chosen Cartesian squares with the exact localized ordinary square
compositor. The proof is complete.

lem-sp-constant-scalar-pullback-cube identifies that compositor with the actual
ambient constant-ring comparator and obtains the forward cube by equality of inverse
isomorphisms. The proof is complete.

Change record: coord/changes/direct-image-scalar-operations.md.

## Second reading by X7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
