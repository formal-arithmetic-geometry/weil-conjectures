## What changed

Proved `AlgebraicGeometry.ProEtale.constantTowerTransition` from the published
coefficient mate's unit factorization and the canonical single-object/H0
identifications. The generic single-complex composition and categorical
cancellation arguments are private, fully proved helpers in the item module.
The target statement, hypotheses, coefficient map, and comparison are preserved.
No resolution or isomorphism is selected arbitrarily.

The implementation repair caches the underived sectionwise coefficient square
with its two composite functor types, hides large comparison/unit/iso bodies
behind `no_expose`, and adds proved characterizing equations in the existing
comparison and H0 modules. The augmentation uses the equal cached H0 iso;
`singleRightDerivedH0Iso_def` proves equality to the original construction.
The canonical exact/single and exact/H0 comparison caches have explicit
functor types and proved defining equations. Rewriting through these equations
avoids the repeated concrete module-structure normalization that caused the
kernel timeout. The complete main file compiles in 51.0 seconds.
`RightDerivedSingleH0` is a public import because the augmentation definition
uses its canonical iso. All original public imports remain.

`RightDerivedSingleCounit` receives two necessary proof rewrites using the new
unit equation. The other nine downstream consumers compile unchanged. All three
adapted dependency modules are unclaimed; no source-library module is changed.
The change record is
`coord/changes/constant-tower-transition-normalization.md`.

The item node now records the unit-compatible mate proof and its two direct
proof dependencies. The other two nodes retain their mathematical statements
and gain the characterizing declarations in their Lean attachments. The
blueprint unit route remains unchanged.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.ProEtale.constantTowerTransition`
(`lem-pod-constant-tower-transition`). There are zero `sorry`s in the item and
zero added in the delivery. No statement is split off. All newly added API
lemmas and all private helpers are proved. The three dependency modules also
contain zero `sorry`s.

Remote consumer validation passed for all five H0 API consumers and all five
other coefficient-comparison consumers. Their compilation times were 3.7–20.0
seconds and 8.4–13.7 seconds respectively. The modified counit compiles in 3.7
seconds. The delivery tool records the final packet compilation and preflight.

## No longer needed

Removed these original private proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleModuleDirectImageLeftExact`.
- `Mathlib.CategoryTheory.Limits.Preserves.Finite`.
- `Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`.
- `Sheaf.CategoryTheory.NormalizedDerivedComparisonCommonResolution`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`.
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`.
- `Mathlib.Algebra.Homology.DerivedCategory.Plus`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.

The explicit three-resolution route no longer needs these direct proof
dependencies: `def-weil-pbc-proetale-site`,
`def-weil-proetale-module-direct-image`,
`lem-sf-kinjective-derived-map-computation`,
`lem-sf-normalized-derived-comparison-common-resolution`,
`lem-sp-grothendieck-enough-injectives`,
`lem-weil-pbc-bounded-below-injectives-kinjective`,
`lem-weil-pbc-kinjective-hom-derived`,
`lem-weil-pbc-left-exact-injective-resolution-degree-zero`,
`lem-weil-proetale-module-direct-image-left-exact`, and
`prop-pur-kinjective-resolutions-exist`.
Statement dependencies remain unchanged. Some of these results remain used
transitively by the comparison or the H0 normalization; no global withdrawal or
module pruning is claimed.

Removed the obsolete tool-use approvals for
`prop-pur-kinjective-resolutions-exist`,
`lem-weil-proetale-module-direct-image-left-exact`,
`lem-sf-kinjective-derived-map-computation`, and
`lem-sf-normalized-derived-comparison-common-resolution`, retaining the
coefficient-comparison approval in its original order. The replacement direct
dependency is the proved `lem-kun-right-derived-single-h0`.

The earlier sandbox's proposed split
`lem-pod-constant-tower-transition-single-unit` is unnecessary: its calculation
is now a proved private generic helper. No such split node or module is added.
No existing declaration or module is removed.

## Where the brief, the DAG or earlier work was wrong

The resolution plan is valid, but the library's existing mate factorization and
canonical H0 normalization provide a shorter proof. The earlier attempt stopped
at concrete derived-category normalization. The required repair is to cache
the underived square with both functor types and expose equations of the large
canonical constructions; a compile timeout is not a tool failure.

The sectionwise square and the single-complex/unit calculation do not require
finite coefficients. Finiteness is used to invert the published comparison.
The argument permits identity coefficient maps, zero maps/objects, empty
schemes, and nonflat restriction such as Z/4 to Z/2. No additional hypothesis,
weakened conclusion, or changed canonical comparison is used.

## Forced adaptations

`Sheaf.CategoryTheory.RightDerivedSingleCounit` (unclaimed) failed against the
hidden unit at its original line 70: `change` was not definitionally equal to
the goal containing `R.singleRightDerivedUnit.app X`. Its original line 183
reported that `dsimp` made no progress. Added
`rw [Functor.singleRightDerivedUnit_app]` before the first `change` and replaced
the second `dsimp` with that rewrite. These are its only changes. Its original
signatures, visibility and imports remain identical. All other consumers
compiled without adaptation.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
