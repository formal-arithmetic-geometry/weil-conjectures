## What changed

Replaced the proof hole of `AlgebraicGeometry.ProEtale.IntegralModelsStacks.discrete_coefficient_local_models` without changing its signature. The proof now constructs the two pullback-stable sieves, transports scheme covers to and from covering sieves on the coefficient-sized site, and glues the local comparisons by transitivity of the topology. The reverse implication uses Mathlib's finite presentation of a finite module over a Noetherian ring and its cokernel universal property. A proved private characterization exposes actual matrices while keeping the internal finite-presentation definition behind an API with an abstract coefficient object.

Two new modules isolate the comparisons for one specified finite matrix: `Sheaf.AlgebraicGeometry.DiscretePointPresentationRefinement` and `Sheaf.AlgebraicGeometry.DiscreteConstantPresentationLifting`. Neither assumes a locally constant or finite-local-model predicate, and neither requires Noetherian coefficients. Both lemmas return actual matrices with the prescribed row and column counts. The parent proves finiteness of their ordinary cokernels from the surjective cokernel projection, and performs the additional work of extracting presentations, passing between finite generation and finite presentation, changing the universe of a cover, and assembling the refinements. This is a decomposition, not a net closure of the mathematical obligation.

`Sheaf.CategoryTheory.FiniteLocalSectionLifts` proves simultaneous lifting of any finite tuple along a locally surjective presheaf morphism. It supplies the finite common-refinement step in the plans of both matrix lemmas. Three new definition modules give typed interfaces to the existing finite free point module, restriction module and point pullback functor. Their bodies are exactly the existing constructions; no data is chosen from an unproved existence theorem. This avoids repeated kernel expansion of the underlying categorical data. The two new matrix statements use these interfaces, and all their consumers are included in this delivery. All seven modules compiled through `lcompile.py --all`; the item took 56.5 seconds with profiling enabled. Profiling settings and the reported long line were then removed for the delivery checks. No existing definition, public import, declaration signature, source-library file, or unit route changes.

## Proved and sorry left

Original holes removed: one, `AlgebraicGeometry.ProEtale.IntegralModelsStacks.discrete_coefficient_local_models` (node `lem-sfb-discrete-coefficient-local-models`). Its proof is complete relative to the two newly stated matrix comparisons. There are zero holes in the item module.

New holes: two, each exactly `:= by sorry` in its own module:

- `AlgebraicGeometry.ProEtale.IntegralModelsStacks.discrete_point_presentation_refinement`, node `lem-sfb-discrete-point-presentation-refinement`.
- `AlgebraicGeometry.ProEtale.IntegralModelsStacks.discrete_constant_presentation_lifting`, node `lem-sfb-discrete-constant-presentation-lifting`.

Fully proved new public declaration: `CategoryTheory.Presheaf.finite_local_section_lifts`, node `lem-sfb-finite-local-section-lifts`, with no holes. All private helpers in the item module are proved. The delivery removes one hole and adds two: it is a decomposition with net one additional hole, not one theorem proved without remaining dependencies.

## No longer needed

No module is withdrawn, and no existing public import is removed. The parent's direct proof dependency on `def-sfb-constant-sheaf-scheme-pullback-comparison` is replaced by dependencies on the two finite-matrix lemmas; the comparison remains needed by those lemmas and is not globally pruned. The parent's existing finite-local-model and section-reconstruction dependencies remain.

The proof uses the existing `CondensedRing.upperStarFromPointModComp` from the private import `WeilConjectures.WeilObject.Sheaf.Stalk` and the composition coherences from `UpperLowerStar.Coherence`. Two redundant draft imports, the pro-etale site wrapper and `ModuleCat.Kernels`, were removed because they are already public dependencies of the statement imports. This does not withdraw either module.

The scalar-normalization route is unused: arbitrary coefficient isomorphisms need only become constant on finitely many entries locally. No global normalization hypothesis is added. The proof does not import `IntegralSectionLocalModels`; its elementary cover calculation is specialized locally, avoiding that module's unrelated integral-model obligations. That module was not an original import and is not claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

No false statement or process defect was found. The prior node's matrix-comparison steps were not already available as Lean lemmas with the required arbitrary coefficient isomorphism and slice restrictions. The updated node exposes these precise remaining steps instead of duplicating the whole local-model equivalence.

Edge cases were checked at the level of the statements and constructions: zero rows or columns still give cokernels of finite free maps; finite tuples include the empty index set; the maximal sieve handles that case; empty covering sieves require no local witnesses; the empty scheme admits its empty cover; zero coefficient rings cause no nontriviality assumptions. No choice of data from an unproved mere-existence theorem is used in a definition. The two unproved comparisons assert properties of actual cokernels and given isomorphisms.

## New nodes

`lem-sfb-discrete-point-presentation-refinement`: forward comparison for a single displayed finite presentation on the condensed point, producing a covering sieve of constant cokernels of ordinary matrices with the same ranks. The remaining work is compatibility of section reconstruction, coefficient change, localization and finite cokernels, followed by finite refinement. Its module is `Sheaf.AlgebraicGeometry.DiscretePointPresentationRefinement`. Both matrix-node plans explicitly use the existing canonical constant-sheaf pullback comparison and weakly-etale slice localization as generic tools; these uses are declared in their split reports, with no change to either tool or its unit route.

`lem-sfb-discrete-constant-presentation-lifting`: reverse comparison for one displayed constant finite matrix and its trivialization, producing locally actual point cokernels with exactly the same ranks as the given ordinary matrix. Its module is `Sheaf.AlgebraicGeometry.DiscreteConstantPresentationLifting`. Together with the forward lemma it leaves the cover assembly and Noetherian algebra to the now-complete parent proof.

`lem-sfb-finite-local-section-lifts`: a fully proved general finite-intersection argument for simultaneous local lifting. Its module is `Sheaf.CategoryTheory.FiniteLocalSectionLifts`; both matrix-node plans depend on it. No existing statement or definition is changed, so no change record is needed.

`def-sfb-point-model-free-module`: Finite free modules on the condensed point. The module `Sheaf.AlgebraicGeometry.PointModelFreeModule` defines `pointModelFree` by the actual existing construction, with its codomain recorded explicitly. It has no holes and no assumptions beyond those of that construction.

`def-sfb-point-model-restriction-module`: Restriction modules with their category recorded. The module `Sheaf.AlgebraicGeometry.PointModelRestrictionModule` defines `pointModelRestriction` by the actual existing construction, with its codomain recorded explicitly. It has no holes and no assumptions beyond those of that construction.

`def-sfb-point-model-pullback-functor`: Point pullback with its module categories recorded. The module `Sheaf.AlgebraicGeometry.PointModelPullbackFunctor` defines `pointModelPullbackFunctor` by the actual existing construction, with its codomain recorded explicitly. It has no holes and no assumptions beyond those of that construction.

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
