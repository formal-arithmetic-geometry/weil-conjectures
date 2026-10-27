## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.integralModelsOperations` with its
signature unchanged. The four clauses are assembled from existing exact pullback,
scalar-model immersion extension, internal support projection, and cohomology APIs.
The private proved helper `tensor_single_noetherian` adapts the already proved
`boundedConstructible_tensor_single` argument: its field-base assumptions are unused
in the proof. It uses common strata, the existing local finite-presentation tensor
calculation, monoidal restriction and vanishing detection. Two finite Postnikov
inductions then give the bounded tensor clause. The adic predicate comparison
recovers exactly the original constant scalar-model convention.

The private proved helper `immersion_projection` composes the open and closed
projection isomorphisms with abstract coefficients. Keeping coefficients abstract
avoids unfolding the concrete valuation-ring construction in these transports.
The original declaration docstring (the initial proof plan) is preserved.

All original public imports remain. Local irreducibility attributes keep derived functor
and inverse-image constructions behind their comparison APIs during elaboration. Explicit
predicate and immersion-assertion types avoid expensive unfolding during isomorphism
transport. Updated the item's proof and proof dependencies
to this implementation; the unit's inverse image, tensor, immersion extension and
projection formula steps remain realized. No source-library declaration is edited.

Change record: `coord/changes/V1-integral-models-operations-proof-context.md`.
It covers the static interface checker's conservative treatment of the added namespace
opens and local elaboration attributes, with every downstream importer listed.
The complete proof compiled cleanly through lcompile.py in 30.7 seconds; the delivery
compilation and axiom probe also passed. The first preflight requested this change record.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.CondensedRing.integralModelsOperations`.
The private helpers `tensor_single_noetherian` and `immersion_projection` are proved too.
Holes closed: 1. Holes added: 0. Holes left in delivered Lean: 0. Split off: 0.
Existing imported theorems remain their own items; no claim of eliminating their
transitive axioms is made. In particular the scalar-model immersion extension
is used as the stage-3 brief requires.

## No longer needed

Removed private imports:

- `WeilConjectures.ConstructibleSheaf.Pullback`
- `Mathlib.AlgebraicGeometry.Sites.Proetale`
- `Mathlib.CategoryTheory.MorphismProperty.Composition`
- `Mathlib.CategoryTheory.Sites.Precoverage`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Mathlib.LinearAlgebra.FreeModule.PID`
- `Sheaf.Algebra.Homology.KFlat`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`
- `Mathlib.CategoryTheory.Sites.Sheafification`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Sheaf.AlgebraicGeometry.NoetherianStratumDetection`
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`
- `Sheaf.Paper.ProjectionMateExact`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.CategoryTheory.RingedSliceExtensionTensor`
- `Mathlib.CategoryTheory.Adjunction.Limits`
- `WeilConjectures.CategoryTheory.SiteMorphismComposition`
- `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale`
- `Sheaf.AlgebraicGeometry.IntegralConstantCompletion`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`

The replacement uses already available internal module operations and finite
presentation calculations, so it avoids a second transport to sectionwise ringed
modules and an explicit scalar cyclic-resolution calculation in this item.
The following old direct proof dependencies are no longer needed here (their
own declarations and other consumers are preserved):

- `lem-sfb-pullback-constant-model-constructible`
- `lem-weil-pbc-locally-noetherian-quasi-separated`
- `def-weil-pbc-sites-and-cohomology`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `lem-weil-l-adic-extension-integers-dvr`
- `det-prop-integral-criterion-constant-coefficients`
- `lem-sfb-flat-dvr-scalar-tensor`
- `lem-weil-pbc-noetherian-stratum-detection`
- `lem-sfb-flat-scalar-cyclic-resolution`
- `lem-sfb-integral-constant-model-heart-closure`
- `lem-sbc-cohomology-in-weak-serre-subcategory`
- `lem-weil-pbc-ringed-projection-mate-exact`
- `lem-sfb-bounded-bifunctor-devissage`
- `lem-sf-open-tensor-normalization`
- `lem-weil-proetale-closed-tensor-projection`
- `lem-weil-pbc-site-morphism-composition`

Removed obsolete top-level tool approvals in their original order:

- `lemma-constructible-pullback-stratification`
- `lem-weil-pbc-proetale-ringed-open-closed`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `lem-weil-l-adic-extension-integers-dvr`
- `lem-weil-pbc-noetherian-stratum-detection`
- `lem-weil-pbc-ringed-projection-mate-exact`
- `lem-weil-proetale-weakly-etale-localization`
- `lem-pc-kflat-resolution`
- `lem-weil-pbc-ringed-slice-extension-tensor`
- `lem-weil-pbc-site-morphism-composition`
- `lem-weil-pbc-sheafification-exact`
- `lem-sfb-pullback-constant-model-constructible`
- `det-prop-integral-criterion-constant-coefficients`
- `lem-sfb-integral-constant-model-heart-closure`
- `lem-sbc-cohomology-in-weak-serre-subcategory`
- `lem-sf-open-tensor-normalization`
- `lem-weil-proetale-closed-tensor-projection`

No module is withdrawn. This report makes no assertion that the unused modules
are globally unreachable; shared consumers may still need them.

## Where the brief, the DAG or earlier work was wrong

The recorded plan and old docstring missed the now-proved internal module
support projection theorem, the adic constructibility predicate comparison,
and the Noetherian local finite-presentation tensor calculation. These give
shorter transports without changing the statement or the unit route.
The existing `boundedConstructible_tensor_single` statement has field-base
hypotheses, but every line of its proof works under Noetherianity alone; the
private helper records that specialization/generalization without changing the
existing public declaration.

The following existing results are used as tools from other units, rather than
replacing this unit's operations steps: `lem-sfb-adic-constructibility-predicate-comparison`
(the exact scalar-model predicate equivalence), `lem-sfb-lfp-tensor-single`
(the local integral tensor computation), `lem-sfb-dc-ell-adic-triangulated` and
`lem-sfb-dc-module-devissage` (finite cohomological induction),
`lem-sfb-condensed-support-projection-formula` (the actual unbounded internal
projection maps), `def-sfb-condensed-pullback-tensor-comparison`
(the canonical support/upper-star identification), and
`det-lem-formal-closed-support-adjunction` (closed image exactness).
Their DAG paths do not depend on this item. No new tool approval is written.

Searches were run via msearch.py: semantic exact inverse-image/cohomology query,
Loogle mapDerivedCategory/bounded query, and grep bounded_mapDerivedCategory_obj.
Local rg searches found the existing exact-functor cohomology APIs, tensor-single
proof, adic comparison, and internal support projection formula.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
