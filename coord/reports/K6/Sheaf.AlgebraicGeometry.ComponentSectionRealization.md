## What changed

Replaced the proof of `component_section_realization` without changing its statement.
The ring map is constructed from tensor-unit global sections, the specified monoidal
inverse image, and α. Its bijectivity follows from full faithfulness. The terminal
section/global-section ring equivalence and preservation of global sections by a
fully faithful strong monoidal additive functor are proved in
`Sheaf.CategoryTheory.SectionRingGlobalSections`.

`ComponentSectionMap` constructs the map and proves its bijectivity under full
faithfulness. `ComponentSectionScalarNormalization` verifies the prescribed point
scalars using β's naturality and monoidal unit equation. `ComponentSectionRealizationPoint`
proves the point realization comparison by `mapModCompIso`, coefficient cancellation,
and the exact derived functor API. All these constructions have actual Lean bodies.

The two remaining parts are separate modules: `ComponentInverseFullyFaithful`
contains the coefficient-independent geometric full-faithfulness assertion, and
`ComponentSectionDerivedSquare` contains the first derived square for the fixed
constructed ring map, with no bijectivity, point-factorization or scalar condition.
These statements are strictly separate parts of the original conjunction. Neither
repackages the original existential theorem.

No existing statement or definition was changed. No source-library module was edited,
no consumer needs adaptation, and no change record is required. The original public
import is preserved; all new imports in the item are private proof imports.

## Proved and sorry left

Original hole closed by decomposition:
`AlgebraicGeometry.ProEtale.CondensedRing.component_section_realization`
(node `lem-zl-component-section-realization`). One original hole replaced by two
strictly smaller holes; this is a decomposition, not a net hole reduction.

Proved without new holes: `component_section_realization_point`,
`component_section_scalar_normalization`, `componentSectionMap_bijective`,
`sectionGlobalEval_bijective`, and `globalMapFunctor_bijective`.
`abelianGlobalEval`, `sectionGlobalEval`, `sectionGlobalEquiv`, and
`componentSectionMap` are explicit constructions with no sorry data or proof fields.

Every remaining sorry (two in the delivery, zero in the item):

- `AlgebraicGeometry.ProEtale.CondensedRing.component_inverse_fully_faithful`,
  node `lem-zl-component-inverse-fully-faithful`.
- `AlgebraicGeometry.ProEtale.CondensedRing.component_section_derived_square`,
  node `lem-zl-component-section-derived-square`.

Each has exactly `:= by sorry`, a source, a complete proof in words, and a new node.
Validation: all seven sandbox modules compile cleanly in import order, including
the final theorem assembly. The item has zero sorry, the two residual modules have
one each, and every other new module has zero.

The new comparison does not choose arbitrary data from an unproved existence theorem:
the ring map is explicit, and full faithfulness only supplies its bijectivity proof.

## No longer needed

No pre-existing Lean import was removed: the original item imported only its model.
A redundant new direct import of `ComponentSectionMap` was removed from the item;
its scalar and derived comparison imports already expose that interface.

The parent proof no longer directly uses
`lem-weil-pbc-condensed-point-basis-evaluation` (`Sheaf.Paper.CondensedPointBasisEvaluation`).
The ring comparison instead uses terminal/global sections and full faithfulness.
The clopen-partition dependency moves to the full-faithfulness lemma.
K-flat preservation, tensor descent and constant realization scalar extension move to
the fixed-map derived-square lemma, and remain needed there. They are not globally
pruned. The point realization comparison requires none of those tensor-descent lemmas.
No module is withdrawn and no declaration in `WeilConjectures` is removed.

## Where the brief, the DAG or earlier work was wrong

The original proof plan treated both realization comparisons by K-flat tensor descent.
The point comparison follows more directly from the already available ordinary
module-object functor-composition isomorphism. The original section-ring proof also
hid the compatibility between the actual monoidal structure on component inverse
image and an adjunction-based evaluation formula. Constructing the map on tensor-unit
global sections keeps the stated arbitrary braided structure explicit; β supplies
the required scalar normalization. There is no claim that the original theorem is false.

The existing module-unit theorem concerns a different chosen component functor and
ringed module pullback, so it cannot be applied verbatim to the specified additive
inverse image. The full-faithfulness residual states precisely that geometric gap.
The unit's statement and realized steps are preserved.

## New nodes

`lem-zl-section-ring-global-sections`: proved terminal/global-section ring equivalence,
in `SectionRingGlobalSections`.

`lem-zl-global-map-functor-bijective`: proved global-section bijectivity for a fully
faithful strong monoidal additive functor.

`def-zl-component-section-map`: explicit fourfold composite of ring homomorphisms.

`lem-zl-component-section-map-bijective`: proved composition of four bijections.

`lem-zl-component-section-scalar-normalization`: proved scalar normalization.

`lem-zl-component-section-realization-point`: proved ordinary module composition,
coefficient cancellation, and exact derived comparison.

`lem-zl-component-inverse-fully-faithful`: geometric residual, with no coefficients
or derived realization in its statement. Stonean evaluation of the actual unit gives
the proof; empty tests are covered by the empty-cover axiom.

`lem-zl-component-section-derived-square`: derived tensor residual for the explicit
ring map. It has no weak-contractibility assumption and does not assert that the map
is an isomorphism or respects point scalars. Its proof follows the source's balanced
tensor maps on flat-term K-flat complexes and localization.

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
