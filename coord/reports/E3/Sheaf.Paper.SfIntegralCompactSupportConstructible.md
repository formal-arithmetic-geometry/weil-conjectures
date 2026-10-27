## What changed

Completed the proof of `WeilConjectures.sfIntegralCompactSupport_constructible` from
named project declarations. The proof gives the middle scheme its actual field
structure, verifies finite type, Noetherianity, quasi-compactness and invertibility of l,
and uses the completed open-reduction comparison. At each finite level the existing
open constructibility theorem preserves the given common interval. The existing
integral direct-image theorem supplies the proper image and its uniform bound.

The proof composes three whole-tower isomorphisms: ordinary consumer to slice proper
system, the existing slice proper/support comparison, and slice support to intrinsic
consumer. A fully proved private helper compares arbitrary Roos limits by rotating
distinguished triangles and taking products of the level isomorphisms. Integral
constructibility then transports through the resulting object isomorphism.

Moved the unchanged tower prefix to `Sheaf.Paper.SfIntegralCompactSupportTower` and
publicly reexported it from the item module, to avoid the new presentation lemma importing
its own consumer. No existing signature or definition body changes. Added a definition
ownership node and the separate presentation theorem module. The extraction record is
`coord/changes/sf-integral-compact-support-tower-extraction.md`.

Validation: all three modules compiled in import order through lcompile.py. After the
presentation interface was narrowed, the item again compiled with the explicit middle
tower comparison. The final packet is recompiled and checked by deliver3.py.

## Proved and sorry left

Original item: one sorry, `WeilConjectures.sfIntegralCompactSupport_constructible`.
That declaration now has a complete Lean proof; zero sorry remains in its module.
The previously proved `sfCompactSupportProjection_transition` remains proved with the
same body in the extracted tower module.

Added one sorry: `WeilConjectures.sfCompactSupportTower_presentation`, in
`Sheaf.Paper.SfCompactSupportTowerPresentation`, node
`lem-sf-compact-support-slice-intrinsic-towers`. It compares the existing normalized
slice functors and their entire towers with the published intrinsic functors and towers.
It has no constructibility conclusion and no constructibility hypothesis. Its six-step
proof and sources are in its docstring and node. It is the genuine presentation lemma
needed between the DAG's independently stated comparison and the consumer. The main
proof supplies the completeness conversion, common finite interval, finite
constructibility, proper image, Roos-limit comparison and isomorphism transport.

Count: one upper hole closed, one lower hole added; this is a decomposition, net zero,
not a claim of a net hole reduction. The added definition module has zero holes. The
already existing sorry in `compactSupportProperImageTower` is imported, not copied or
counted as newly added. Other dependencies retain their existing proof status.

## No longer needed

No module is withdrawn. The open-then-proper route of the unit is retained. The proof
uses the already stated completeness and strict reduction conclusions of
`IntegralOpenReduction.Comparison`, so it needs no separate K-flat or Roos-preservation
proof in this module. Those results may remain needed by the comparison theorem itself.
The closed complement and extended stratification are supplied by the proved
`open_finite_constructibility_interval`, not constructed again in the consumer.

The generic derived-limit morphism and levelwise-isomorphism nodes are not imported:
the private proved helper uses Mathlib's isomorphism completion of rotated distinguished
triangles directly. No global pruning of their other users is claimed.

Removed direct imports from the original item (some remain transitive dependencies
of the retained comparison theorems):

- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Mathlib.CategoryTheory.Adjunction.Limits`
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`
- `Mathlib.Topology.Constructible`
- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.AlgebraicGeometry.ProEtaleDirectImageRestrictionOfScalars`
- `Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage`
- `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`
- `Sheaf.CategoryTheory.RingedSliceExtensionTensor`
- `Sheaf.CategoryTheory.Triangulated.DerivedLimitMorphism`
- `Sheaf.Paper.DerivedComplete`
- `Sheaf.Paper.DerivedCompleteOnSlices`
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`
- `Sheaf.Paper.IntegralReductionTowerWellDefined`
- `Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted`
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`
- `Sheaf.Paper.SfDerivedDirectImage`
- `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction`
- `WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence`
- `WeilConjectures.Compactification.Refinement`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek`

The six original public statement imports are available transitively through the new
tower module. None is removed from the public dependency surface.

## Where the brief, the DAG or earlier work was wrong

The rework row points to a quarantined copy, but the current source exists and its
baseline compiles. No quarantined attachment was withdrawn. The previous A6 proof
already closed the projection-transition helper; the current item has only the one
constructibility hole.

The DAG's `compactSupportProperImageTower` uses slice extension and
`coefficientProEtaleModuleDirectImage`; the consumer uses the published intrinsic
extension and constant derived direct image. The named tower theorem therefore does
not typecheck as the required comparison without a real presentation argument. The
new result isolates precisely that argument and requires the section and K-injective
normalizations already present in the operation records. It is not a renamed
constructibility theorem.

Finite-field-only `OpenTensorQuotientAugmentation` cannot be substituted here: the
item allows an arbitrary base field. The auxiliary finite field used in the private
completeness conversion is only an index in the legacy definition and adds no geometric
base-field assumption. Empty opens, identity opens, the zero complex and arbitrary
coefficient levels preserve the stated interval and comparison formulas.

## New nodes

`def-sf-integral-compact-support-tower` owns the existing tower prefix in its extracted
module. It introduces no new mathematical object and changes no transition; the old
names and bodies are preserved and publicly reexported. Its own primary declaration is
`WeilConjectures.sfCompactSupportTerm`; the other nine moved declarations are listed in
its Lean record.

`lem-sf-compact-support-slice-intrinsic-towers` states the separate presentation lemma
for arbitrary normalized open/proper records and all derived-complete inputs. It
compares functors and inverse systems, with no constructibility assertion. Its detailed
proof is the coefficient/adjunction normalization part of the source's compactification
construction. Three kinds of search found only generic tools, not this specialized
comparison. Change record: `coord/changes/sf-integral-compact-support-tower-extraction.md`.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
