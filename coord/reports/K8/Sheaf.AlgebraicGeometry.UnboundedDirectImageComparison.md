## What changed

Proved `AlgebraicGeometry.ProEtale.unboundedDirectImageComparison`, with its original
signature and specified canonical mate unchanged. The proof chooses a common lower
truncation in each homology degree, uses the canonical bounded-below comparison there,
and cancels the two truncation maps in the mate's naturality square. Homology detects
isomorphisms in the unbounded derived category.

Extracted `unboundedDirectImagePullbackIso` and `unboundedDirectImageComparisonMap`
verbatim into `Sheaf.AlgebraicGeometry.UnboundedDirectImageComparisonMap`, publicly
reexported by the original module. Proved the mate's naturality. The new
`UnboundedDirectImageBoundedBelow` proves compatibility of the specified unbounded
adjunction with the D+ adjunction, including the counit and inverse-image square;
this identifies the actual canonical mate with the existing invertible D+ mate.

`UnboundedDirectImageTruncationStability` proves both tail estimates. Finiteness of A
makes module sheaves torsion. Classical higher-direct-image vanishing, the canonical
module/abelian comparison and faithful forgetting give cohomological dimension
`d = 2 dim(X) + 1` for etale direct image. The proved
`isLE_rightDerivedFunctor_obj_of_dimension` bounds its total derived functor.
For the target, exact comparison commutes with truncation, the bounded-below mate
bounds every truncation uniformly, and exact countable products plus the existing
source-library left-completeness theorem give an upper bound with one extra degree.
The derived direct image preserves products as a right adjoint. With `N = m-d-2`,
the two long exact truncation sequences prove stabilization in degree m.

The fixed-ring product instance is the proved
`AlgebraicGeometry.Scheme.ProEt.countableAB4Star` in
`WeilConjectures.AlgebraicGeometry.ProEtale.Replete`; this realizes the constant-ring
case of `det-pe-products-exact` directly in `Sheaf (ModuleCat A)`. No conversion to
ringed-site modules, coefficient-universe change, or arbitrary comparison is chosen.

The existing fully proved `WeilConjectures.CategoryTheory.DerivedCategory.LeftComplete`
was missing its published compiled artifact. An unchanged sandbox copy compiles in
5.6 seconds; it contributes no source diff to the delivery. Its generic uniform
truncation-bound theorem now has an explicit DAG attachment. All four changed/new
Sheaf modules compiled together (0.2, 0.2, 12.5 and 4.4 seconds before warning cleanup).
The three unchanged direct consumers were also checked against the extracted definitions:
`FiniteComparisonLocalizing`, `FiniteRingCompactSupportProjection`, and
`FiniteRingSiteTensorTranspose`. Their temporary copies are not part of the delivery.

Change record: `coord/changes/K8-unbounded-direct-image-mate-extraction.md`.
No existing consumer is adapted, and no target statement changes. The unit's direct-image
comparison and its canonical bounded-below/truncation route are retained.

Resumed-session validation (2026-10-19): reread all four Sheaf modules and the existing
left-completeness proof against current sources. The first required dry run found two
metadata defects in the new attachment node: added the missing LeanSearch record after
running that search, and omitted lean.file for the existing declaration as required by
the delivery checker. Retained the four existing tool approvals still used by the subarguments, in their
original order; only the six obsolete approvals are removed. No Lean statement or
proof changed during this metadata repair.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.unboundedDirectImageComparison`
(`lem-sfb-unbounded-direct-image-comparison`). Original holes: 1; closed: 1; added: 0;
remaining in the item and all delivered Lean files: 0. No open statement is split off.
This is a proof from existing project declarations; their upstream holes remain their
own items, as required by this stage.

Also fully proved:

- `AlgebraicGeometry.ProEtale.unboundedDirectImageComparisonMap_naturality`.
- `AlgebraicGeometry.ProEtale.unboundedDirectImageComparison_boundedBelow`, together
  with `restrict_derived_adjunction`, `included_counit`, and `included_pullback`.
- `AlgebraicGeometry.ProEtale.unboundedDirectImage_truncation_stability`, together
  with `module_higher_bound`, `source_stable`, and `target_upper_bound`.

The existing generic left-completeness theorem and its helpers are already proved;
the unchanged source copy contains no holes. No hollow definitions or new axioms occur.

## No longer needed

The shorter target estimate removes the entire sectionwise route. The following old
proof dependencies are no longer used for this item's argument (their independent
uses elsewhere are unaffected):

- `det-pe-unbounded-classical-truncation` / `Sheaf.SixFunctors.UnboundedClassicalTruncation`:
  the generic left-completeness theorem and bounded-below mate give the target bound.
- `sk-thm-pe-classical-sheaves` / `Sheaf.AlgebraicGeometry.ProEtaleClassicalSheaves`:
  no sectionwise classical-cohomology predicate is needed.
- `lem-sf-finite-cd-derived-upper-bound` /
  `Sheaf.CategoryTheory.DerivedCategory.FiniteCDDerivedUpperBound`: replaced by the
  existing proved theorem for the specified total `rightDerivedFunctor` in
  `Sheaf.CategoryTheory.RightDerivedFunctorUpperBound`.
- `lem-sfb-unbounded-sections-localization` /
  `Sheaf.CategoryTheory.Sites.UnboundedSectionsLocalization`,
  `lem-pur-kinjective-restrict-localized` / `Sheaf.Algebra.Homology.KInjectiveRestrictLocalized`,
  `lem-weil-proetale-weakly-etale-localization` /
  `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`, and
  `lem-weil-pbc-right-adjoint-preserves-kinjective` /
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`:
  no evaluation or localized K-injective comparison is used.
- `lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison` /
  `Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison`: the proof uses only
  `det-pbc-conventions-module-cohomology` for ordinary higher direct images.
- `def-weil-pbc-ind-etale-algebra` / `Sheaf.RingTheory.IndEtaleUniverseTransport`,
  `def-weil-pbc-ind-etale-basis`, and `lem-weil-pbc-ind-etale-basis`:
  no additional basis-evaluation or sheafification argument is needed here.
  The affine-site module remains an upstream dependency of the existing comparison.
- `lem-weil-pbc-kinjective-hom-derived` and
  `lem-weil-pbc-ringed-site-module-sheafification-exact`: no separate K-injective
  hom calculation or sheafification detection is needed.

The truncation-stability module imports
`Mathlib.Algebra.Homology.DerivedCategory.HomologySequence` where it is used;
the main module needs no direct import of it. Preserved the original
public imports to preserve the interface. Removed all abandoned section-bound and
classical-upper-bound modules and nodes from the never-delivered sandbox sources;
no repository module is withdrawn. Their holes are absent from this delivery.

Pruned the old top-level tool approvals for
`lem-sf-finite-cd-derived-upper-bound`, `lem-weil-pbc-ind-etale-basis`,
`lem-pur-ringed-site-grothendieck-abelian`, `lem-weil-proetale-weakly-etale-localization`,
`lem-pur-kinjective-restrict-localized`, and
`lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison` from the item's
node. Their relative order and the remaining approvals are preserved. The relevant
Grothendieck instances are already supplied by the category interfaces, without
invoking the ringed-site realization as an extra step.

All direct proof imports removed from the item (some remain needed through the
new strict-subargument modules, so these are not all global prunings):

- `Sheaf.RingTheory.IndEtaleUniverseTransport`.
- `WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.
- `Sheaf.AlgebraicGeometry.ModuleCohomologyConventions`.
- `Sheaf.AlgebraicGeometry.ProEtaleClassicalBounds`.
- `Sheaf.SixFunctors.UnboundedClassicalTruncation`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`.
- `Sheaf.Algebra.Homology.KInjectiveRestrictLocalized`.
- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`.
- `Sheaf.CategoryTheory.DerivedCategory.FiniteCDDerivedUpperBound`.
- `Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`.
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`.
- `Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.
- `Sheaf.AlgebraicGeometry.ProEtaleClassicalSheaves`.
- `Sheaf.AlgebraicGeometry.ClassicalContinuityMap`.
- `Sheaf.AlgebraicGeometry.ClassicalDerivedDefinitions`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`.
- `Sheaf.CategoryTheory.Sites.UnboundedSectionsLocalization`.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox reduction left a section estimate open and attempted coefficient
transport across different universe presentations. That reduction is superseded:
left completeness works directly in the fixed-ring categories, so the estimate is
unnecessary. The DAG's prescribed sectionwise proof was longer than needed below
the unit level. The new route still proves both truncation tails and uses the
specified bounded-below canonical comparison; it does not bypass a unit statement.

The stabilization proof does not use the prime/invertibility or primary-annihilation
hypotheses beyond finiteness of A; its original new-helper interface is retained
with unused names prefixed by underscores. The original theorem signature is unchanged.
Empty schemes, zero rings, negative cutoffs and complexes unbounded in both directions
are covered: all bounds use homology and exact products, with no nonempty/nonzero or
boundedness assumptions introduced.

## New nodes

`def-sfb-unbounded-direct-image-mate` records the two verbatim constructions and their
proved naturality in `UnboundedDirectImageComparisonMap`.

`lem-sfb-unbounded-direct-image-bounded-below` records the proved compatibility of the
canonical D+ and total-derived mates in `UnboundedDirectImageBoundedBelow`.

`lem-sfb-unbounded-direct-image-truncation-stability` records the two proved tail
estimates and long exact sequence arguments in `UnboundedDirectImageTruncationStability`.

`lem-sfb-derived-left-complete-truncation-bound` attaches the existing fully proved
`DerivedCategory.isLE_obj_of_forall_isLE_obj_truncGE` and its left-completeness helpers
in the source library. It is genuinely generic (no schemes, ring, mate or direct image),
adds no Lean declaration and no hole, and gives the Milnor-triangle argument in its
proof steps. DAG searches found no attachment for these declarations; the existing
`lem-sfb-left-complete-heart-upper-bound` instead assumes normalized left completeness
and a bound on a class of heart objects, so it is not the theorem used here.

Change record: `coord/changes/K8-unbounded-direct-image-mate-extraction.md`.

## Second reading by K8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
