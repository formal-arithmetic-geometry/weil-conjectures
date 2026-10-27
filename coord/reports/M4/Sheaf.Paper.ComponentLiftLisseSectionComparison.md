## What changed

Replaced the single hole in `component_lift_lisse_section_comparison` by a complete
combination proof. `normalized_naturality` proves the unit-normalized Hom formula from
the inverse monoidal comparison's unit equation and naturality. The private
`component_sections_bijective` uses the displayed derived dual pairing, essential
surjectivity of the component equivalence, and full faithfulness on the unit and N to
construct two bijective parametrizations by Hom(1,N). It proves that section pullback
intertwines those parametrizations and cancels the source bijection. The proof uses the
existing proved `isLisseCoefficientModule_upperStar` for lisse pullback.

Factored the unchanged auxiliary definitions and exactness instances into
`Sheaf.Paper.ComponentLiftSectionDefs` to let three independent proof obligations import
them. The item publicly reexports this module and all its former public imports. All
original signatures, bodies, attributes and visibility are preserved; only blueprint
tags and declaration ownership change. No source-library module is changed.

Change record: `coord/changes/M4-component-lift-section-data-factorization.md`.

Validation: all five Lean modules compiled through `lcompile.py`. The support modules
compiled in 45.0, 34.0, 34.9 and 35.2 seconds; the final main module compiled cleanly in
29.0 seconds. Profiling options were removed before that final compile. A source check
also verified the original theorem signature verbatim and every moved declaration body
verbatim apart from the new owning blueprint tag. No direct importer needs adaptation.

## Proved and sorry left

Original holes removed: 1 of 1, by declaration name
`AlgebraicGeometry.ProEtale.CondensedRing.component_lift_lisse_section_comparison`.
This is a decomposition, not a completed proof of all mathematics: 3 holes are added.
The original theorem has a complete Lean proof from the three strictly separate
obligations and the existing lisse-pullback theorem. The normalized Hom calculation and
the section-bijectivity deduction are proved directly in Lean, without further holes.

Every remaining hole in the delivery is exactly a public theorem with `:= by sorry`:

- `AlgebraicGeometry.ProEtale.CondensedRing.component_lift_geometric_comparisons`
  (`lem-sfb-component-lift-geometric-comparisons`): construction and coherence of
  component pullbacks and their equivalence on dualizable objects; source steps 1 and
  the equivalence input of step 5.
- `AlgebraicGeometry.ProEtale.CondensedRing.component_lift_finite_free_duality`
  (`lem-sfb-component-lift-finite-free-duality`): the local finite-free dual and the
  K-flat and derived pairing statements; source steps 3 and 4, for arbitrary schemes.
- `AlgebraicGeometry.ProEtale.CondensedRing.component_lift_section_normalization`
  (`lem-sfb-component-lift-section-normalization`): evaluation at one, its pullback
  equation and the section naturality, identity and composition laws; source steps 6
  and 7, for arbitrary modules and morphisms. It does not assert section bijectivity.

The data module contains zero holes. No definition chooses new data from an unproved
mere existence assertion. Edge cases checked in the argument and split statements:
empty component spaces/schemes, zero coefficients, zero rank, varying ranks, identity
maps and arbitrary scheme maps in the two local assertions.

## No longer needed

The item removes these former private proof imports:

- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`
- `Sheaf.Paper.CondensedFiniteFreeTensorExact`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`

The geometry and duality obligations retain the relevant imports and DAG dependencies;
this is a reassignment to genuine separate proof steps, not a claim those modules are
unused throughout the library. The finite-upper-star exactness API is already available
through the unchanged public imports. The parent's former direct dependencies are now
owned by the split steps, except its step-2 glue is replaced by the existing proved
`lem-sfb-lisse-module-inverse-image`. No module or unit route is withdrawn. No globally
pruned module is claimed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement is changed or disputed. The required lisse-pullback clause
already has a proved library declaration, so its cover-construction glue need not be
repeated. The large original statement requires auxiliary definitions to be factored
before the source's independent steps can be stated in separate modules. Its original
blueprint ancestry has a null `from.node`: `tools/blueprint_refs.py ancestor` also
computes null because the inherited `created.item` chain is broken above the item.
The new nodes retain that inherited ancestry result and name the intended blueprint
source `det-thm-sf-ctf-stability-direct-images`, through
`lem-sfb-admissible-direct-image`, explicitly in `from.place`. No existing ancestry
metadata is changed.

## New nodes

`def-sfb-component-lift-section-data` owns the original auxiliary data and constructions,
unchanged and publicly reexported. It introduces no hole.

`lem-sfb-component-lift-geometric-comparisons` is the geometric construction, equivalence
and coherence subargument, with no finite-free or section assertion.

`lem-sfb-component-lift-finite-free-duality` is local finite-free duality, with no component
space or contractibility assumption and no section comparison.

`lem-sfb-component-lift-section-normalization` is the elementary evaluation and
functoriality subargument for arbitrary modules; bijectivity of actual section pullback
is proved in the parent from this normalization and the two other obligations.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
