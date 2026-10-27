## What changed

Replaced the sorry in `AlgebraicGeometry.ProEtale.IntegralModelsStacks.constant_slice_module_encoding` by an explicit categorical assembly. Transport coordinates directly along U.hom ≫ f, apply the global encoding comparison there, and compose fixed-scalar inverse images before localizing to the slice. The global encoding is the existing internal/sectionwise module equivalence, transport along AsSmall, scalar restriction along the given ring isomorphism, and the proved fixed-scalar equivalence. Its comparison with direct image is the identity on sections; linearity uses the pulled-back equation on constant sections. Conjugating the specified adjunctions gives the inverse-image comparison.

Added `Sheaf.AlgebraicGeometry.ConstantModuleGlobalEncoding`, proving the global equivalence, its explicit functor equation, its regular-module comparison and its coordinate-normalized inverse-image comparison. This proved component is separated because the original full assembly repeatedly unfolded its equivalence implementation during kernel checking. Private irreducible wrappers, proved functor and section-encoding equations, and an abstract categorical assembly avoid unfolding the constructions in the final proof. The main proof uses proved access lemmas for the explicit global and slice constructions; its coordinate choice is fixed by the proved uniqueness assertion.

Added `Sheaf.AlgebraicGeometry.CoefficientSliceFixedModuleEquivalence`, proving coefficient-sized weakly-etale localization for fixed-scalar module sheaves, including the inverse-image and constant-sheaf comparisons. Its site equivalence is the existing concrete localization conjugated by AsSmall. The inverse-image comparison follows from composition/base-change adjunction, and the constant comparison from commuting precomposition with sheafification.

Added `Sheaf.AlgebraicGeometry.ConstantCoefficientPullbackCoordinates`, constructing the transported arbitrary ring coordinates and proving their uniqueness using the constant-sheaf and inverse-image adjunctions. It is used once along the composite U.hom ≫ f. Added `Sheaf.AlgebraicGeometry.CondensedCoefficientRingPullback`, which explicitly constructs the commutative-ring coefficient map and isolates invertibility of its adjunct as the sole remaining obligation. That obligation has no k, c, module or slice. The private regular-module identifications and scalar equivalence proofs follow the already proved constructions in DiscretePointPresentationTransport; that module itself is not imported.

The fixed-scalar compositor follows the general adjunction calculation already used in NoetherianGlobalConstructibility; that module is not imported. No existing declaration signature, public import, shared definition, target statement or other existing Lean module changed.

## Proved and sorry left

Closed the one original hole, `AlgebraicGeometry.ProEtale.IntegralModelsStacks.constant_slice_module_encoding`, by reduction to one strictly smaller coefficient-ring statement. Added one hole, `AlgebraicGeometry.ProEtale.IntegralModelsStacks.condensedSmallRingMap_pullback_isIso`, node `lem-sfb-condensed-coefficient-ring-pullback`. This is a decomposition of one hole into one, not an unconditional proof of the item.

Proved `AlgebraicGeometry.ProEtale.IntegralModelsStacks.constant_module_global_encoding`, node `lem-sfb-constant-module-global-encoding`, `AlgebraicGeometry.ProEtale.IntegralModelsStacks.constant_coefficient_pullback_coordinates`, node `lem-sfb-constant-coefficient-pullback-coordinates`, and `AlgebraicGeometry.Scheme.coefficient_slice_fixed_module_equivalence`, node `lem-sfb-coefficient-slice-fixed-module-equivalence`, with no sorry. The item module has no sorry. No sorry occurs in a definition or private helper.

The remaining coefficient-ring lemma has its source and complete proof in words in its docstring and node. The map is explicitly constructed from coefficientMap; the postponed assertion is only its adjunct's invertibility. The coordinate construction and uniqueness are now proved: the constant-sheaf/global-sections adjunction shows the canonical constant-ring inverse-image map is invertible, and cancellation in the inverse-image adjunction determines d. The statement includes the zero ring, the empty scheme, and arbitrary coefficient automorphisms; no normalization of c is imposed.

## No longer needed

The internal-module pullback compositor `CondensedRing.upperStarComp` and the intermediate coordinate/encoding on Y are unnecessary: transport directly along U.hom ≫ f and use composition of fixed-scalar inverse images instead. The compositor is retained upstream. None of the original public imports or declared mathematical proof dependencies is pruned. Weakly-etale localization remains used through the new proved fixed-scalar lemma; internal module operations, the constant-ring module equivalence, integral-model data and constant sheaves remain used. No upstream declaration or module is removed. No finite-presentation or finite-discrete hypothesis is used. FiniteComparisonModelRealization is imported for its general fixed-scalar equivalence and its explicit restriction comparison; its specialized finite-coefficient results are not used.

## Where the brief, the DAG or earlier work was wrong

No false original statement was found. The DAG's internal-compositor step is replaced by fixed-scalar composition; its slice comparison can be proved using the ordinary site equivalence and composition/base-change adjunction, without a separate ringed module localization obligation. The remaining interface gap is invertibility of the reconstructed commutative-ring coefficient adjunct. The original alpha_f is already invertible on abelian sheaves; its compatibility with the reconstructed commutative-ring inverse image is the isolated step. Transport of arbitrary c is now a proved categorical consequence.

## New nodes

`lem-sfb-constant-coefficient-pullback-coordinates`: proved construction and uniqueness of arbitrary ring coordinates from the invertible coefficient adjunct, with its equation on constant sections.

`lem-sfb-condensed-coefficient-ring-pullback`: the sole new hole. It asserts invertibility of the explicit coefficient-map adjunct, independently of k, c, all modules and all slices. Its source is the actual invertible alpha_f, transported through reconstruction and the algebraic forgetful comparison.

`lem-sfb-constant-module-global-encoding`: proved global equivalence and direct/inverse-image comparison on arbitrary coordinates satisfying their constant-section equation, with the regular-module comparison.

`lem-sfb-coefficient-slice-fixed-module-equivalence`: proved localization for fixed-scalar module sheaves, including restriction of inverse image and preservation of constant sheaves. It realizes the fixed-scalar localization part of step 2 without an additional hole.

Validation: lcompile.py --all compiled all five Lean files with exit code 0, no warnings, and every file within the 60-second limit. The original statement and public imports match the shared source exactly; all five node attachments and dependency IDs were checked.

No change record is required: the delivery changes only the assigned module, its node, and new modules and their nodes.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
