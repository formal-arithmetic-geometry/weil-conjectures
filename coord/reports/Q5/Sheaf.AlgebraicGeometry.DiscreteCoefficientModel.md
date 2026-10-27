## What changed

`Sheaf.AlgebraicGeometry.DiscreteCoefficientModel` retains every existing public signature,
public import and definition body. The proof now constructs its coefficient isomorphism from
the proved `discreteRingIso` construction in `IntegralModelsFlatResidue`, constant-sheaf
precomposition, and the specified ring equivalence. Naturality of sheafification and the existing unit equations prove the
normalization formula, rather than selecting a coefficient map from an existence theorem.

The proved `sectionMonoidal_exists` helper of `FiniteComparisonPresentation` supplies the
section-module monoidal structure. The new
`Sheaf.CategoryTheory.RingedCocontinuousMonoidal` proves the complementary strong monoidal
restriction theorem: presheaf scalar restriction is strong when the coefficient map is an
isomorphism, cocontinuity makes its sheafification comparison invertible, and the Mathlib
monoidal-localization universal property descends the structure to module sheaves. This
handles the independent universes of the original pro-etale site and its small model.

The constructibility argument uses `discrete_coefficient_local_models` on each stratum,
then the already proved `proEtale_noetherian_global_constructibility` and its finite-local-
presentation conversion. The new local-model theorem is the remaining finite-matrix step.
There are no changes to source-library modules, existing public interfaces or target statements.

The private coefficient-map construction is irreducible; the normalization proof unfolds it
explicitly and uses the existing unit equations. The theorem scopes out seven broad integral-
coefficient instances and supplies fixed-universe sheafification and commutativity proofs.
The composite tensor structure is transported through Mathlib pushforward composition and
functor associativity to the defined model functor. Local irreducibility keeps the section
functor, reconstructed ring, model functor and small-site transport from repeatedly expanding
during this comparison. The existing additive comparison is also kept abstract locally. These are proof-local choices and add no public instance or interface change.

## Proved and sorry left

The one original hole, `AlgebraicGeometry.ProEtale.IntegralModelsStacks.discrete_coefficient_model`,
is closed by a complete Lean proof from the new local-model statement. Its coefficient-map
existence, normalization and monoidality clauses are proved without new holes. The unchanged
normalization-uniqueness, equivalence and additivity proofs remain in place.

`SheafOfModules.ringed_cocontinuous_monoidal` is proved, with no holes in its module.

One hole is added:
`AlgebraicGeometry.ProEtale.IntegralModelsStacks.discrete_coefficient_local_models`
in `Sheaf.AlgebraicGeometry.DiscreteCoefficientLocalModels`, node
`lem-sfb-discrete-coefficient-local-models`. Its proof is exactly `by sorry` and its docstring
contains the finite-matrix proof in both directions, the covering-family/sieve conversion,
and the empty-scheme and zero-ring cases. It asserts only the local-model comparison after
restriction along a scheme morphism. It asserts no normalized coefficient map, tensor
structure, stratification or global constructibility equivalence. Thus this is a decomposition:
one original hole closed, one strictly smaller hole added, net hole reduction zero.

Validation: the joint server compile passed with no warnings: local-model statement 31.3 s,
monoidal restriction 3.5 s, and assigned module 53.7 s. All three files compile alone within
60 seconds. No profiling or diagnostic options remain.

## No longer needed

None. No existing imports, declarations, modules or unit steps are withdrawn. The existing
scalar-restriction tensor module is still used for its proved cancellation isomorphism.
The unit's coefficient-comparison route is retained.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The planned monoidal argument needs attention to universes:
the site object, site morphism and coefficient universes cannot be identified in the small-site
transport. The new restriction proof works with essentially small sites and explicit coefficient
universes. The local-model comparison may allow an arbitrary coefficient sheaf isomorphism:
only finitely many matrix entries occur, so refine the covering until their images (or inverse
images) in the constant ring sheaf are all constant. Normalization is still proved and retained
in the parent theorem.

Searches found Mathlib's `Localization.Monoidal.functorMonoidalOfComp`, presheaf monoidal
pushforward, and discrete condensed-module comparisons. They did not find the project-specific
finite local-model comparison. Existing `FiniteConstantLocalModel` supplies the finite-matrix
characterization; `ScalarNormalizedConstantModels` does not itself identify this small-site
transport and its scheme-pullback restrictions. The new node records the actual searches.

## New nodes

`lem-sfb-ringed-cocontinuous-monoidal` records the proved generic monoidal restriction result.
It is a proof-level tool for the tensor clause, with no new data chosen from an unproved
existence theorem. Its proof uses the fully proved restriction-sheafification and scalar-tensor
helpers of `SemilinearDerivedCalculus` and Mathlib monoidal localization.

`lem-sfb-discrete-coefficient-local-models` records the remaining local finite-matrix step.
It is strictly smaller than the assigned normalized, monoidal, global model theorem. Its
statement was checked for empty schemes, the zero ring, identity restrictions, and arbitrary
locally varying automorphisms of the constant ring sheaf. The parent node's proof and
dependencies follow the implemented route. No change record is needed: no existing statement
or definition changes.

The `lem-ctf-finite-comparison-presentation` dependency supplies only its fully proved
generic section-monoidality helper. The finite comparison theorem itself is not used; the
helper packages the internal-section tensor theorem already in the assigned route.

## Second reading by Q5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
