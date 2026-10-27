## What changed

Proved six of the seven existing theorems of
`Sheaf.AlgebraicGeometry.CondensedLocalizationExactCohomology`, with unchanged signatures.
Localized restriction is additive sectionwise. The actual module pullback is additive
because its right adjoint is additive, and preserves finite colimits by adjunction.
Finite-limit preservation follows from the existing internal/sectionwise transport
statement and exactness of the internal condensed pullback.

The representative comparison composes the actual derived-functor factorization with
the termwise complex isomorphism induced by the supplied localization comparison.
For cohomology, proved a private generic lemma for an exact functor between abelian
categories: invert the short-complex homology comparison, precompose the two derived
functors with Q, and descend the resulting isomorphism through fully faithful
precomposition with Q. The map-preimage identity proves the required normalization
on every complex. Specialize this lemma to the actual pullback.

A private instance supplies the existing abelian structure for coefficient modules.
There are no new public definitions, modules, nodes or changed statements.

## Proved and sorry left

Closed six of seven original holes:

- `AlgebraicGeometry.ProEtale.CondensedLocalization.localizedPullback_additive`
- `AlgebraicGeometry.ProEtale.CondensedLocalization.pullback_additive`
- `AlgebraicGeometry.ProEtale.CondensedLocalization.pullback_preservesFiniteLimits`
- `AlgebraicGeometry.ProEtale.CondensedLocalization.pullback_preservesFiniteColimits`
- `AlgebraicGeometry.ProEtale.CondensedLocalization.localized_complex_represents`
- `AlgebraicGeometry.ProEtale.CondensedLocalization.cohomology_comparison`

The one retained original hole is
`AlgebraicGeometry.ProEtale.CondensedLocalization.localization_comparison`.
Its original statement, source, full proof docstring and DAG plan are retained.
No holes added or split off. Finite-limit preservation uses the existing theorem
`InternalModuleOperations.internal_module_operations_transport`, whose proof hole
is outside this delivery. This does not assert that the targets are axiom-free.

## No longer needed

Removed unused private imports of
`Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`,
`Sheaf.CategoryTheory.LocalizedModuleExactForSystems`, and
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.
The proved instances and derived comparisons use the actual adjunction,
internal/sectionwise exactness transport and Mathlib's localization APIs.

No node or module is withdrawn. The unfinished localization comparison still needs
its existing proof dependencies, so none of those DAG dependencies is pruned.
No source-library declaration or public import is removed.

## Where the brief, the DAG or earlier work was wrong

The generic cohomology API recorded as `CategoryTheory.Functor.homologyFunctorIso`
is `CategoryTheory.ShortComplex.homologyFunctorIso` in the pinned Mathlib.

An adjunction-based candidate proof of localization was developed and repeatedly
compiled. Its unresolved point was the kernel conversion in the coefficient ring
section formula: the reconstructed ring's underlying additive map must be compared
with `condensedPullbackHom` after the canonical inverse localization isomorphism.
The conversion repeatedly unfolded the condensed inverse-image and sheafification
constructions, exceeding the file's 60-second compile limit. Generic evaluation,
explicit function equalities, normalized ring homomorphisms, and endpoint reductions
were tested. That candidate and its unused private helpers are not delivered.
The original localization hole remains, rather than transferring it to a new item.

Read the source passages at Stacks 03CE (sites.tex,
lemma-localize-given-products), 03EK (sites-modules.tex, section-tensor-product),
010N (homology.tex, lemma-exact-functor), 015F (derived.tex,
lemma-right-derived-exact-functor), and the current scalar-six blueprint unit.
The six proofs preserve all hypotheses and apply to all integer degrees and
unbounded complexes. No choices are made from unproved mere existence statements.

## Second reading by P9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
