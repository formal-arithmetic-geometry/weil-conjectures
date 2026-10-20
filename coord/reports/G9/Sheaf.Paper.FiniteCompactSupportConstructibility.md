## What changed

Repaired the returned delivery's missing-source import: the comparison theorem is in
`WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison`, not the
nonexistent `Sheaf` module. Updated both applications to its current declaration name,
`isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf`. All three sandbox modules
compile together after this repair. No signature or definition changed.

Replaced the `sorry` in
`AlgebraicGeometry.Scheme.finiteCompactSupportConstructibility` with a complete assembly
proof, without changing any existing declaration's signature or definition. The private
transport lemmas identify intrinsic bounded constructibility with the existing fixed-scalar
predicate, identify the compactification candidates, and transport the source library's
proved constructibility and `[a,b+2e]` estimates. A direct ideal calculation supplies the
invertible coefficient exponent, including in characteristic zero. Triangulation follows
from exact open extension and the triangulated right derived functor.

The coefficient clause uses the theorem
`AlgebraicGeometry.Scheme.finiteCompactSupportScalarComparison` in the new module
`Sheaf.Paper.FiniteCompactSupportScalarComparison`. The main module independently proves
constructibility of the comparison's target and then its source, and supplies the interval
bound. That theorem now has a complete assembly proof: descend the input to the etale
site, identify the actual etale reduction by the canonical scalar/site isomorphism,
reflect its cohomological interval, apply the canonical transport identity, and
conjugate by the input isomorphism using the proved naturality of the scalar transpose.
No finite Tor hypothesis is introduced.

The new `Sheaf.Paper.FiniteCompactSupportScalarTransport` constructs the etale proper/open
scalar isomorphism, the intrinsic-realization scalar isomorphism, the site scalar
isomorphism, and their compact-support composite. Its remaining named statement is
`AlgebraicGeometry.Scheme.FiniteCompactScalar.intrinsicCompactScalarIsoOfOrigin_hom`:
the equality identifying that explicit composite with the specified intrinsic scalar
transpose. This is the presentation-normalization part of the argument, for arbitrary
finite commutative rings and bounded-below etale inputs. It asserts no constructibility,
interval, or scalar invertibility result. All comparison objects are constructed from
recorded functors and adjunctions; no arbitrary existence witness is chosen.

Updated the parent node's proof route and added three DAG records: one attaches the already
proved source-library finiteness/amplitude declarations, one records the now-assembled coefficient comparison, and one records the separate
canonical scalar-transport identity. All new proof imports are private. No change record is needed:
existing public signatures, definitions and public imports are unchanged.

Validation: all three delivery modules compile together through `lcompile.py --all` against
the current server library. The theorem's signature agrees with the current source.

## Proved and sorry left

Closed one original hole, in
`AlgebraicGeometry.Scheme.finiteCompactSupportConstructibility`
(node `prop-finite-compact-support-constructibility`). Its module now contains zero
`sorry` occurrences; all private helpers are proved.

The intermediate `AlgebraicGeometry.Scheme.finiteCompactSupportScalarComparison`
(node `lem-finite-compact-support-scalar-comparison`) is also proved. Its earlier retained
`sorry` was removed in this session, rather than delivered.

One new hole remains, in
`AlgebraicGeometry.Scheme.FiniteCompactScalar.intrinsicCompactScalarIsoOfOrigin_hom`
(node `lem-finite-compact-support-scalar-transport`), whose proof is exactly `by sorry`.
Across the delivery this is one original upper hole closed and one lower normalization
hole added, net zero: a decomposition. The finite constructibility, amplitude, actual
reduction interval reflection, scalar comparison at an etale origin, and naturality
assembly are written in Lean. The remaining equality is the scalar-mate site/realization
normalization, not a restatement of finite compact-support constructibility.

Its source is the canonical comparison portion of Steps 7--10 and the existing
`etaleProEtale_scalar_mate` lemma. The equality still requires identifying the open
left-adjoint uniqueness map, comparing the intrinsic K-injective normalization with
fixed-scalar direct image, and cancelling the normalized site/realization squares.
The module docstring and new node give that argument explicitly. Nearby
`reductionDirectImage_isIso` and finite-reduction coefficient-change declarations
impose extra finite-Tor, positive-characteristic or separated-base hypotheses and
cannot simply be applied to this statement.

## No longer needed

The following direct proof imports were removed from the item module:

- `Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison` (nonexistent;
  replaced by the source-library module above)
- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.AlgebraicGeometry.ProperBoundedConstructible`
- `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons`
- `Sheaf.AlgebraicGeometry.CompactifiableOverField`
- `Sheaf.AlgebraicGeometry.DerivedCategories`
- `Sheaf.CategoryTheory.TruncationTriangle`
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
- `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`
- `Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.GroupTheory.Torsion`
- `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection`
- `Sheaf.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.AlgebraicGeometry.EtaleRestrictScalarsAdjunctionIdentities`
- `Sheaf.Algebra.Homology.ChangeOfRingsTensorComparison`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`
- `Sheaf.AlgebraicGeometry.FiniteTypeSheafFiniteness`
- `Sheaf.CategoryTheory.BoundedHeartAmplitude`
- `Sheaf.Paper.CompactSupportDirectImageTriangulated`
- `Sheaf.Paper.PurEtaleScalarMateProjection`
- `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction`
- `WeilConjectures.ConstructibleSheaf.OpenClosed`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek`

The unit-route imports `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel`,
`Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, and
`Sheaf.Paper.CompactificationCoherence` are retained as required by the unit-route check.

These removals are direct-import pruning, not a claim that all these modules disappear
from the targets' transitive import closure. The fixed-scalar source finiteness theorem
already contains the sheaf/truncation argument, and the coefficient split retains the
proper projection, open tensor, scalar-mate and canonical site-comparison dependencies.
The original parent-node proof dependencies below are no longer direct dependencies of
its assembly proof; needed lower ingredients are recorded under the fixed-scalar or
coefficient-comparison node instead:

- `def-weil-compact-support-candidate`
- `def-weil-proper-morphism`
- `def-weil-finite-type-morphism`
- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-sf-proetale-constructible-origin`
- `def-weil-finite-torsion-constructibility`
- `lem-sf-comparison-pullback-exact`
- `prop-weil-pbc-site-comparison-finite-level`
- `lem-sf-class-compact-support-comparison`
- `lem-weil-pbc-extension-by-zero-exact`
- `lem-fin-extension-by-zero`
- `lem-fin-proper-bounded-constructible`
- `lem-amb-etale-compact-comparisons`
- `sbc-thm-finiteness-finite-type`
- `lem-weil-pbc-left-exact-injective-resolution-degree-zero`
- `lem-weil-pbc-module-sheaves-enough-injectives`
- `prop-weil-pbc-kinjective-resolutions-exist`
- `def-kun-projection-formula-map`
- `lem-pur-bounded-heart-amplitude`
- `lem-compact-support-direct-image-triangulated`
- `lem-pur-derived-change-of-rings`
- `lem-pur-change-of-rings-tensor-comparison`
- `lem-kun-0f0g`
- `lem-pur-etale-open-derived-tensor`
- `def-pc-kflat-complex`
- `lem-pur-etale-scalar-mate-projection`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `lem-sf-compact-support-restriction-of-scalars`

In particular, the separate generic `lem-pur-bounded-heart-amplitude` and
`lem-compact-support-direct-image-triangulated` statements are bypassed: the already
proved fixed-scalar amplitude theorem supplies the former argument, and existing
triangulated instances supply the latter. No blueprint unit statement or realized
proof step is bypassed. No existing module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The returned packet depended on a compiled comparison interface without a matching
tracked source module. Its import and short theorem name were stale. The repair uses
the tracked source-library comparison and its full current theorem name; no replacement
module or compatibility declaration is introduced.

The earlier retained report called the scalar-comparison module and its node existing,
and said no new node was added. They are absent from the shared source and are new in
this delivery. The fixed-scalar finiteness record is also new, but attaches existing
proved declarations rather than introducing another Lean theorem or another hole.
The retained report also failed to list the removed imports and to identify the
one-for-one hole replacement as a decomposition; these are corrected above.

The dispatch reference clock was reset externally on the retained sandbox at
2026-10-19 18:24:54 UTC. The retained checkpoint identifies the preceding attempt
as the compile-server-failure attempt (try 2 of 5); `.brief2` through `.brief5`
now carry the same restart timestamp. This continuation preserved the prior Lean
work and did not modify `.budget`. The compiler now answers and all three modules
compile. This reset is dispatcher metadata, not a proof obstacle.

The first complete preflight found three metadata errors: an existing-declaration
record unnecessarily set `lean.file`, and two new `lean.statement` fields were not
verbatim copies of their Lean signatures. These are corrected. Its unit-route
classification also required retaining the three imports listed above.

The current source's target statement is unchanged. The bounded-domain qualification
on ordinary derived reduction is essential; no finite-Tor hypothesis was added.

## New nodes

`lem-finite-compact-support-fixed-scalar-finiteness` records the existing declarations
`AlgebraicGeometry.ProEtale.boundedConstructible_rightDerivedLowerShriek` and
`AlgebraicGeometry.ProEtale.constructibleIn_rightDerivedLowerShriek` in
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Finiteness`.
It adds no Lean declaration and no hole.

`lem-finite-compact-support-scalar-comparison` records the proved strict
coefficient-comparison theorem in `Sheaf.Paper.FiniteCompactSupportScalarComparison`.
Its source is the parent blueprint proof, Steps 7--10. Its docstring includes the
zero-object, empty-scheme and equal-level edge cases and the canonical-map normalization.
There are no change-record paths because no existing statement or definition changed.

`lem-finite-compact-support-scalar-transport` records the separate equality of the
canonical scalar transpose with the explicitly constructed transported proper/open
scalar isomorphism. Its source is the scalar-mate compatibility lemma and the intrinsic
realization/K-injective normalization in Steps 7--10. This is the only new hole.

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
