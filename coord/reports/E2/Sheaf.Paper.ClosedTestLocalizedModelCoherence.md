## What changed

Proved the original conjunction from explicit representative/homotopy and naturality
calculations, and four independent
geometric substatements. The original theorem signature is unchanged.

Moved the concrete maps and predicates to ClosedTestLocalizedModelData so the independent
substatements share their precise interface without importing the theorem they support.
All original declaration names are publicly reexported. Factored localizationUnit through
the universal derived-evaluation unit; localizationUnit_eq_original proves equality with
the original termwise formula. evaluationLocalization has the same body. The four test-object aliases become ordinary definitions with unchanged bodies, and the
fibre-test return types explicitly name the original site types. This avoids eager
expansion of nested fibre products during elaboration. Evaluation and evaluationLocalization retain their bodies as ordinary definitions;
complex sections remains an abbreviation. ev_additive supplies evaluation additivity
without unfolding. localizationTransformation packages the localization unit as a
natural transformation, so resolution naturality is its naturality equation.
The sourceUnit and targetUnit definitions are irreducible components of explicit natural
transformations. sourceUnit_eq_original and targetUnit_eq_original prove equality with
the original composites; the proof uses their naturality without expanding those composites. Change record:
coord/changes/closed-test-model-localization-api.md.

The representative proof uses K-injectivity only of the target complexes. It constructs
both comparison maps using the existing Hom-bijection, obtains the square up to homotopy,
and applies additive evaluation. Universal derived-unit naturality proves all four
resolution comparison squares. The test-map calculation is retained as an independent
geometric result: the three ordinary/derived evaluation squares and the two slice
localization squares must use the same presheaf restrictions.

## Proved and sorry left

Closed the one original body of
AlgebraicGeometry.ProEtale.ClosedTestLocalizedModelCoherence.closed_test_localized_model_coherence
by a complete assembly from the four substatements below and the explicit resolution proofs.
This is a decomposition, not a complete proof of the mathematics: one hole closed and
four holes added, for net minus three. The item's module has zero sorry bodies.

Every retained hole is a public theorem in its own new module:

- closed_test_comparison_test_naturality — lem-sfb-closed-test-comparison-test-naturality:
  all five presheaf test squares, with the actual model arrow and specified units.
- closed_test_localized_restriction_normalization —
  lem-sfb-closed-test-localized-restriction-normalization: the actual slice-unit restriction
  calculation after cancelling the supplied resolution.
- closed_test_derived_comparison_normalization —
  lem-sfb-closed-test-derived-comparison-normalization: the two geometric section
  normalization equations, their pinned comparison isomorphisms, and invertibility of
  the two actual localization units.
- closed_test_geometric_section_coherence — lem-sfb-closed-test-geometric-section-coherence:
  transport of ringed-slice localization and its normalized mate to internal modules,
  followed by the restriction square and section cube. The canonical mate unit and counit equations remain part of this geometric result.

The common data module has zero holes and no data chosen from an existence theorem.
Existing imported sorries are used as intended by stage 3, under the four geometric subresults; they are not new delivery holes.

## No longer needed

The item no longer imports the following proof dependencies directly:
WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteAdjunction,
Sheaf.CategoryTheory.Sites.UnboundedSectionsLocalization,
Mathlib.CategoryTheory.Adjunction.Mates,
Sheaf.Paper.SheafSliceDerivedComparison,
Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition,
Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization.
Sheaf.Paper.ClosedTestKInjectiveSectionModels also moves from the direct assembly to
the normalization proof dependency. Their geometric work remains explicitly needed by the retained substatements; their
modules are not globally pruned. The direct item proof uses the new substatements and
Mathlib K-injective comparison. No module is withdrawn.

The direct generic resolution calculation does not need
WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties as a private
proof import; the data still retains the closed-site constructions.

The separate appeal to lem-exc-closed-site-adjunction and
lem-weil-pbc-conjugate-iso-unit-equation is unnecessary for the explicit chain-level
naturality calculations. The geometric substatement uses the canonical mate directly,
with its unit and counit, rather than choosing an isomorphism between adjoints.
The exact internal-module equivalence and slice comparison are still required below
the new geometric bridge statements; they have not been declared globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was weakened or disputed. The generic ringed-slice theorem
is in section-ring module categories, while the item uses internal module objects with
fixed coefficient and pullback comparisons. Instantiating it requires the separately
stated transport/normalization work; it is not a direct application.

ResolutionCoherence quantifies over the alternative resolution and derived morphism;
its transition, uniqueness and homotopy assertions are proved under those binders.
No sibling or parent closed-test theorem is used, avoiding the existing parent/child
DAG cycle risk. The common data module is a statement-interface extraction needed for
these independent results; it is not a split of the theorem to bypass a compile limit.

The edge cases of the new statements were checked against their formulas: zero complexes,
identity test maps, zero and unit ideals (including empty closed tests), and different
K-injective resolutions. None of the retained formulas inverts the closed restriction.

## New nodes

- def-sfb-closed-test-localized-model-data owns the existing concrete maps and predicates
  in the shared data module and their proved original-formula API.
- lem-sfb-closed-test-comparison-test-naturality retains the five test squares as one
  geometric naturality statement, independently of resolution changes.
- lem-sfb-closed-test-localized-restriction-normalization isolates the slice unit equation
  evaluated on the supplied resolution and the cancellation of Q(j).
- lem-sfb-closed-test-derived-comparison-normalization isolates the canonical geometric
  section formulas, independently of transition maps and localization cubes.
- lem-sfb-closed-test-geometric-section-coherence isolates weakly etale localization of
  derived adjunctions and section comparisons, independently of all model resolutions.

Each theorem node has its source, proof in words, Lean signature, dependency record,
Mathlib searches and inherited blueprint ancestry. The original unit route is retained.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
