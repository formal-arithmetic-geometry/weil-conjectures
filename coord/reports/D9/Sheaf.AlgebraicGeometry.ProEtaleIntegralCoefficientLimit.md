## What changed

Proved `AlgebraicGeometry.ProEtale.sfb_integral_coefficient_limit` with its original
statement. The proof constructs finite representability, the positive profinite limit
cone, its scheme limit, the pulled-back representation and the completed representation.
It then constructs the canonical ring comparison, proves invertibility and its normalized
finite projections, and proves uniqueness using the point adjunction.

The point-ring-map lemma is now proved: local surjectivity of constant-presheaf
sheafification reduces finite operations to constant labels; naturality in finite labels
handles paired labels. Joint injectivity of the ring-limit projections proves addition,
multiplication, zero and one for the continuous-function map. It is bundled as a ring-sheaf
morphism. A concrete pushforward/ring-object comparison gives the required monoid morphism.
The ring-comparison lemma transposes it through `Adjunction.mapMon` and identifies its
underlying map by Yoneda and the adjunction unit.

The nine original data definitions are relocated verbatim into
`ProEtaleIntegralCoefficientData`, publicly re-exported from the original module, to avoid
an import cycle. No original statement or definition body changes. The change record is
`coord/changes/sfb-integral-comparison-data-relocation.md`.

Validation: the four delivery modules compile in import order without warnings
(data 0.1 s; point ring map 35.9 s; ring comparison 10.5 s; assembly 33.2 s).
The unchanged consumers `IntegralModelsStacks`, `ProEtaleCoefficientComparisonsPullback`,
`IntegralCriterionReductions` and `SmoothPurityReductionTowerNormalized` also compile against
the delivered modules without warnings. They are not delivered. A fresh source comparison
verified all nine relocated declaration texts and the original theorem signature unchanged.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.sfb_integral_coefficient_limit`
(`det-prop-sfb-qlbar-colimit-x-integral-limit`). Added zero holes. No `sorry` remains in
any of the four delivered modules; the net textual hole reduction is one.

Both new intermediate theorems are proved in this delivery:
`AlgebraicGeometry.ProEtale.sfb_integral_point_ring_map_exists`
(`lem-sfb-integral-point-ring-map`) and
`AlgebraicGeometry.ProEtale.sfb_integral_ring_comparison_exists`
(`lem-sfb-integral-ring-comparison-exists`). No unfinished statements are split off.
The existing integer-tower and other imported project theorems retain their own status.

## No longer needed


Removed direct proof imports Sheaf.AlgebraicGeometry.Sites.ProetaleSiteProperties, Sheaf.AlgebraicGeometry.CoproductCopiesMorphismsClopen, Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage, Sheaf.CategoryTheory.SiteInverseImageTensor, Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects and Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects from the assembly module. Also removed the direct proof imports Sheaf.Topology.ProfiniteCondensedRing and WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic; the latter remains available through the unchanged public interface. The original public imports Mathlib.CategoryTheory.Sites.ConstantSheaf, Sheaf.AlgebraicGeometry.ProEtalePointPullback, Sheaf.Topology.ContinuousMapCondensedRing, Sheaf.NumberTheory.Padics.IntegersProfiniteTower and Sheaf.Paper.CompletedIntegralConstantMapOfUniverses move to the data module and remain publicly re-exported. The smaller obligation uses the concrete sectionwise ring-object and continuous-pushforward APIs; the abstract Cartesian algebraic-object lemmas are no longer required. Finite constant representability uses the clopen theorem through its existing proved module.

The absolute-value-extension and valued-DVR quotient lemmas are no longer direct dependencies of the assembly proof: the existing integers-profinite-tower theorem supplies their whole needed conclusion. Scheme-limit preservation uses the existing locally-constant-ring right adjoint, avoiding a separate cofinal-finite-quotient calculation. Sectionwise set-limit and Yoneda/adjunction facts are supplied directly by Mathlib. No entire shared module is asserted unreachable.

The parent node withdraws these seven direct tool approvals: lem-galois-coproduct-copies-morphisms-clopen (now used through the proved finite-representation module); det-pe-topos-functoriality-site (the source subcanonical-site instances suffice); det-pe-topos-functoriality-inverse-image (the source base-change continuity instance suffices); lem-weil-pbc-left-exact-site-inverse-image-tensor, lem-weil-pbc-sheaf-algebraic-structures-objects and lem-weil-pbc-adjunction-lifts-group-ring-objects (replaced by the concrete ring-object and monoidal-adjunction APIs); and lem-weil-l-adic-extension-integers-dvr (encapsulated in the existing integer-tower theorem). These are direct-dependency removals, not claims that their modules have left the whole targets' import closure.

## Where the brief, the DAG or earlier work was wrong

Earlier attempts stopped during compile-service outages and retained a point-ring-map
hole. The service now responds. The retained arithmetic draft needed explicit quotient-ring
function types: inferring addition and numerals on the carrier of an abstract tower object
fails. Explicitly unfolding only the finite level identifies its labelled section without
expanding the whole profinite construction. The constant-sheaf operation helpers were generalized privately to an arbitrary site,
with explicit weak-sheafification hypotheses, and unfolding is restricted to the comparison
rewrites. The section ring type is explicit when bundling the map, avoiding repeated
reduction of the pushforward. These repairs and the bundling proof close the remaining
hole without increasing the compile limit or changing any original definitions.

The earlier retained ring helper had claimed normalization for arbitrary cone projections;
the replacement explicitly requires the actual quotient projections. Its proof uses precisely
this condition. The limit hypothesis in the point lemma is harmless and unused: joint
injectivity comes from the completed ring-sheaf limit, not from this chosen profinite cone.
No original project statement is disputed or changed. Temporary diagnostic files are kept
outside `lean/` and are excluded from the delivery.

## New nodes

`lem-sfb-integral-point-ring-map` is proved in
`Sheaf.AlgebraicGeometry.ProEtaleIntegralPointRingMap`. It constructs only the ring map on
the profinite point, including finite-operation calculations and naturality.

`lem-sfb-integral-ring-comparison-exists` is proved in
`Sheaf.AlgebraicGeometry.ProEtaleIntegralRingComparison`. It transposes that map through the
monoidal adjunction and proves the specified underlying-map identity; the assembly supplies
invertibility and uniqueness. Both are separate parts of the source's ring-structure step.

The existing node `def-sfb-integral-comparison-coefficients` records the verbatim relocation.
Change record: `coord/changes/sfb-integral-comparison-data-relocation.md`.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
