## Worker report

Item: lem-sp-chart-finite-ring-adjunction. Module:
`Sheaf.SecSmoothPurity.ChartFiniteRingAdjunction`. Main statement:
`AlgebraicGeometry.ProEtale.ChartFiniteRing.chartFiniteRingAdjunction`.
All new theorem proofs are `sorry`; all definition data are real compositions,
full-subcategory lifts, or the explicitly written result structure. No source or
shared-library file was changed.

Source read: current main-20261015 blueprint,
`sec-smooth-purity/sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md`,
Charts paragraph, and the item's seven proof steps. The ordered coordinate model
is the existing `AlgebraicGeometry.affineTraceTower Y d`, identified with ordinary
affine d-space by its existing polynomial-coordinate comparison. Its projection is
`affineTraceProjection Y d`. In dimension zero both are literally the base/identity.

Hypothesis and clause correspondence:

* A field of positive characteristic: `k`, `[Field k]`, `[CharP k pchar]`,
  `hp : 0 < pchar`. The prime different from the characteristic is
  `ell`, `[Fact ell.Prime]`, `hne : ell ≠ pchar`.
* The two finite unital commutative rings and their unital homomorphism are
  `{A B}`, `[CommRing A]`, `[CommRing B]`, `[Finite A]`, `[Finite B]`, `_φ : A →+* B`.
  `n`, `hA`, `hB` give the same annihilator `ell ^ n`. Primality ensures it is
  positive, including `n = 0`. The map is context for this assertion: no scalar
  compatibility equation is claimed by this node, and no flatness is assumed.
* Separated finite-type k-schemes: the `Over (Spec (.of k))` structures and the
  three instances `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` on their
  structural maps. The separated etale finite-type chart is `e` with its four
  corresponding instances. `_he` says its composite with the projection is a
  k-morphism. The chart map g is literally `e ≫ affineTraceProjection Y d`.
* `cp` and `cg` are arbitrary specified compactifications. Their middle schemes
  are proper over Y, hence separated finite type over k. Their base structures
  are canonical composites. No restriction to a preferred compactification is made.
* `etaleProperty R T` is the existing bounded constructible object property
  intersected with the universal degree-zero-module finite-Tor test. Its
  `FullSubcategory` retains every ambient derived morphism. `proEtaleProperty`
  is the existing finite-coefficient comparison-origin presentation with the full
  pro-etale Tor test. The result field `Datum.intrinsic` explicitly equates it,
  on every Noetherian T, with the explicit intrinsic predicate: bounded cohomology, intrinsic finite
  stratifications for every cohomology sheaf, and an ordered finite Tor interval.
  Thus intrinsic constructibility is a conclusion, not an origin assumption.
* The existing scalar-extension functor and derived change-of-rings interface are
  imported. The notation T_T is context only in this node, so this theorem adds
  neither a scalar-compatibility conclusion nor a scalar-preservation assumption.
* Finite Tate twists use the recorded `Scheme.finiteEtaleTateTwist` (equivalently its signed extension at a natural degree). In
  `geometricRight`, its exact comparison image is placed in degree zero, tensored
  by the actual derived tensor, and shifted by `2 * (d : ℤ)`.
* The ordinary right functor `etaleRight` is the full-subcategory lift of
  `Etale.affineTraceRight R N hR Y d ⋙ Etale.ordinaryFinitePullback R e`.
  The first factor is the existing ordered expression for p* (-)(d)[2d],
  with the coordinate tensor/shift/pullback identifications of affine-space trace.
* `Datum.hEt`, `hRight`, `hPro` are conclusions of membership preservation for
  ordinary compact support, the ordinary geometric right functor, and pro-etale
  compact support. They are result fields, never theorem assumptions.
* `affineLeftOnPlus` uses the existing bounded-below coordinate comparison,
  its unbounded compatibility, and the common-refinement comparison to cp.
  `chartLeftOnPlus` combines this with exact sum-extension compatibility and
  the recorded graph-normalized `etaleAmbientLeftComparison` to cg.
  The ordinary adjunction is `Datum.adjEt`. Its field `etaleCounit` says its
  actual counit is the inverse of this left comparison, followed by the counit
  of the exact sum adjunction composed with the ordered affine adjunction.
  The latter is literally `Adjunction.comp`, so its counit is sum evaluation
  followed by affine integration.
* `Datum.hU`, `hV`, `eU`, `eY`, `heU`, `heY` assert that the exact comparison
  restricts to the equivalences on U and Y. The equalities bind their forward
  functors to the actual comparison; their inverses are the specified quasi-inverses.
* `Datum.cf` has the exact orientation C_Y F_et ≅ F_pro C_U. Its
  `fixedComparison` equation requires its inverse to be the published
  `fixedCompactSupportComparisonIso` on the existing bounded-below inclusion,
  with only the endpoint equalities from `heU`, `heY`. It is not a freely chosen
  compact-support isomorphism.
* `Datum.adjPro` has right functor
  `eY.inverse ⋙ etaleRight ... ⋙ eU.functor`, exactly C_U H_et Q_Y in
  composition order. `proCounit` is the requested displayed formula; the first
  factor is the explicit quasi-inverse unit endpoint identification, the next
  is `cf.inv`, and the last is C_Y of the *same* `adjEt` counit.
* `Datum.geometric` is a natural isomorphism from the transported right functor
  to `geometricRestriction`, whose objects and arrows are exactly those of
  `geometricRight`. `geometric_normalization` pins every component to the
  canonical coordinate tensor/pullback/shift comparison and the equivalence
  counit; see the returned-delivery repair section below.
* `Datum.brown` quantifies over any given Brown adjunction on the same localizing
  closures. It concludes restriction preservation and the unique natural iso
  theta from `geometricRestriction` to that Brown restriction. The displayed
  equation equates F(theta) followed by the Brown counit with F(geometric.inv)
  followed by the specified transported counit. Thus theta is explicitly on the
  geometric functor, with its canonically transported counit.
* The main theorem concludes Noetherianness and invertibility of N, rather than
  adding them as assumptions. It then works for every graph-normalized comparison
  datum and normalized ordered affine adjunction datum, separately for A and B,
  concluding the conjunction of their nonempty result records. These are the
  choices specified in the node, with no arbitrary left/right functors supplied.

Dependency declarations read and used (full signatures/docstrings inspected):

* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`; the setting
  is rendered directly by the theorem's structural-map hypotheses.
* `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, derived homology and boundedness.
* `Sheaf.Paper.ProEtaleFixedModuleConstructible`:
  `AlgebraicGeometry.Scheme.IsConstructibleProEtaleFixedModuleSheaf`, directly in the intrinsic-domain equality.
* `Sheaf.AlgebraicGeometry.RingedProEtaleTorAmplitudeOfUniverses`:
  `CategoryTheory.HasRingedSiteTorAmplitudeOfUniverses` and the retained coefficient
  interfaces. In fixed-module coordinates the existing site-independent
  `DerivedCategory.finiteTorAmplitude` is the same universal module test.
* `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer`: its `AdjunctionTransfer`
  namespace's `etaleProperty`, `proEtaleProperty`, `comparison`, `etaleToPlus`,
  `etaleLowerShriek`, `proEtaleLowerShriek`, `localizingLowerShriek`, `toLocalizing`,
  `brownRestriction`, and the transfer theorem.
* `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`:
  `AlgebraicGeometry.ProEtale.scalarExtensionFunctor` (context).
* `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel` (context).
* `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist`:
  `Scheme.finiteEtaleTateLine`, `Scheme.finiteEtaleTateTwist` (equivalently its signed extension at a natural degree).
* `WeilConjectures.Compactification.RefinementCategory`:
  `AlgebraicGeometry.Compactification.Refinement`; canonical comparison ownership.
* `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification` and Plus
  compatibility. The pro-etale constant-module analogue is used from the transfer
  module's public imports.
* `Sheaf.SecSmoothPurity.ReductionDirectImage`:
  `AlgebraicGeometry.ProEtale.reductionDirectImage_isIso` (context).
* `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`:
  `Etale.etaleAmbientLeftComparison`,
  `Etale.derivedEtaleLowerShriekUpperStarAdjunction`.
* `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace`:
  `Etale.exists_affineSpaceTopTrace` and its publicly imported constructed
  `affineTraceAdjunction`, `affineTraceLeft`, `affineTraceRight`,
  `affineTraceCompactSupportComparison`, `affineTracePlusCompatibility`.
* `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`:
  `ProEtale.siteComparisonDerivedPullbackPlus`; its ambient exact termwise functor
  `comparisonUpperStar.mapDerivedCategory` is used by the restricted comparison.
* `Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian`:
  `ProEtale.finiteTorComparisonNoetherian`, the generic proof input for the
  equivalences and intrinsic domain identification, in its small-model coordinates.
* `Sheaf.AlgebraicGeometry.FiniteComparisonClassAdjunction`:
  `ProEtale.fixedCompactSupportComparisonIso`, fixed component in `fixedComparison`.
* `Sheaf.Paper.FiniteLocalizingExceptionalPreservation`:
  `ProEtale.CondensedRing.localizingExceptionalAdjoint_preserves_finiteConstructible`,
  supplying the Brown restriction after the existing coefficient identifications.
* Mathlib `CategoryTheory.Adjunction.comp` and `rightAdjointUniq`, with their
  counit-component and transpose formulas; the finite-type Noetherian and
  quasi-compactness statements recorded on the Mathlib proof dependency were read.

The unstated proof dependencies `lem-sp-etale-ctf-chart-domain`,
`lem-sp-chart-left-scalar-normalization`, `lem-sp-finite-compact-support-domains`
have no recorded modules at the time of writing. They are named in the complete
proof docstring; no fabricated imports or substitute theorem hypotheses are used.
Their missing proofs do not prevent writing this statement with `sorry`.

Edge cases checked before/following elaboration: d = 0 (identity tower and its
identity ordered adjunction); U empty and Y empty; the zero ring (including N = 1,
n = 0); arbitrary characteristic-p base field, with no algebraic-closure or finite
field restriction; nonflat coefficient maps such as Z/ell² → Z/ell; arbitrary
normalized compactification choices; zero complexes; ordered finite Tor bounds
against all module sheaves, including nonconstructible test sheaves. Site universes
are the existing small-site object universe u+1, morphism universe u, coefficient
universe u+1 and derived localization universe u+1. No universe equality on those
site universes is imposed.

Searches actually run through msearch.py:

* leanfinder: "Finite torsion ring etale affine chart compact support adjunction
  transported to proetale constructible finite Tor category with its fixed counit".
  Eight hits, on condensed counits, etale forgetful functors, etale ring algebra,
  and an affine-limit statement; no matching chart theorem.
* loogle: "CategoryTheory.Adjunction, CategoryTheory.Equivalence". Six hits:
  equivalence adjunctions, composition, transport of sheafification adjunction,
  and algebra/coalgebra equivalence; no finite-ring chart theorem.
* grep: "chartFiniteRing|finiteRingChart|proetale.*[Aa]djunction". Zero Mathlib hits.
* leansearch: "Finite torsion ring etale affine chart compact support adjunction
  transports to proetale constructible finite Tor categories preserving its counit".
  Eight hits on condensed/local-constant adjunctions, etale ring algebra and
  topological modules; no match.
* rg of project and upstream for chart adjunction/finiteRing names and the node id:
  no existing declaration of this theorem. `ReductionExceptional` contains
  related chart helpers belonging to its larger coefficient-compatibility theorem.
  It is deliberately not imported: that downstream module's proof uses this item.
  The bounded-below left comparisons here instead reuse the upstream affine trace
  and graph-normalization interfaces directly.
* rg for intrinsic fixed-module constructibility and finite-Tor predicates found
  the same intrinsic predicate in `exceptionalTransportProEtaleObjects`. The repair
  writes this predicate inline from its recorded constituent definitions, without
  importing that theorem module or adding its unlanded theorem node.

Prior-packet validation: prescribed scompile.py checked both sandbox and final library
module successfully, 12.6 s and 12.9 s. The initial repair dry run also passed
at 69474c5266e. These do not validate the subsequent semantic repair. No
`STATEMENT-DISPUTED` finding or statement correction.

## Second reading by O4

Read the live item, saved delivery, maintainer return and the Charts source together.
Two mismatches in the previous packet were real: the extra statement dependency
merely owned an incidental definition, and a bare geometric isomorphism did not
pin the counit in geometric coordinates. The repair removes that dependency,
writes the three intrinsic-domain conjuncts directly, and fixes every geometric
component to the canonical ordered affine normalization, site monoidality,
pullback interchange, degree-zero Tate comparison and equivalence counit.
The Brown uniqueness clause now starts from the actual geometric restriction.
All finite-ring/common-annihilator and separated-chart hypotheses, arbitrary
compactifications, both ring cases and the no-flatness scope remain as before.
The ordinary counit, fixed compact-support comparison and displayed transported
counit remain the same accepted equations. The canonical coordinate recursion
covers dimension zero; the intrinsic predicate and all equations cover empty
schemes, zero rings, zero complexes and nonflat coefficient maps. No second agent
was started, in accordance with the dispatcher instruction. The point-by-point
repair and its source check follow.

## Returned delivery repair

H2: removed `lem-sf-etale-proetale-exceptional-transport` from stmt_deps and
removed its module import. `Datum.intrinsic` now uses boundedness,
`Scheme.IsConstructibleProEtaleFixedModuleSheaf` on every cohomology sheaf, and
`DerivedCategory.torAmplitudeIn` with ordered finite bounds directly. These are
already recorded constituent notions. No new definition node or dependency module
is needed and no theorem is cited merely to access an incidental definition.

H3: `Datum.geometric` is now an actual natural isomorphism to the full-subcategory
restriction of `geometricRight`. `geometric_normalization` fixes every component
at every pro-etale input, using the actual comparison endpoint equality on U,
`chartGeometryComponent` at the specified quasi-inverse origin, and the actual
`eY.counitIso` on Y. Thus an independent minus-identity twist cannot satisfy the
same equation (except where it is itself the identity).

`chartGeometryComponent` is defined by real data: comparison applied to
`etaleChartNormalComponent`, the comparison functor's CommShift isomorphism, the
published derived strong monoidal comparison, the exact degree-zero Tate
comparison, and the site/pullback interchange. `etaleChartNormalComponent` pulls the
canonical affine normalization through the etale chart, combining inverse images.
`affineRightNormalComponent` uses the canonical Tate pullback and signed product maps
whose normalization is already fixed on roots, pure tensors and evaluation.
Its tower recursion starts with identity pullback, the tensor unit and shift zero;
the successor uses pullback/tensor compatibility, tensor associativity, the
normalized product of Tate powers, and addition of shifts. The prior public
`affineTraceRight_normalForm` theorem forgets this map by returning `Nonempty`;
its private normalization helper is not a public usable interface. The chart
helpers expose precisely this canonical composite rather than selecting an
arbitrary witness of that theorem. Each helper belongs to this node, has its
source docstring and is included in lean.declarations.

`Datum.positive` and `flatTwist` are auxiliary conclusions, not added hypotheses:
N is a positive prime power and each finite Tate power is a locally free line
where N is invertible. The canonical maps depend only on these propositions,
not arbitrary choices of bases, orientations or coefficient-flatness assumptions.

`Datum.brown` now states the unique natural isomorphism from
`geometricRestriction`, whose underlying functor is literally `geometricRight`,
to the Brown restriction. Its counit equation is
F(theta) followed by epsilon_Brown = F(geometric.inv) followed by epsilon_pro.
Consequently the right side is exactly the transported geometric counit, while
`proCounit` itself retains the node's original displayed formula. Both canonical
normalization and the Brown identification are statements on whole derived
functors and all ambient morphisms.

The original finite-field/ring/chart/compactification hypotheses, including zero
rings and nonflat coefficient maps, remain unchanged. The item statement and
proof fields are unchanged, and its dependency list returns to the live list.

## Second reading by O4 (repair)

Read the saved packet, the immutable-head return and the current live node. The
initial dry run passed, but the two mathematical return points remained and were
repaired explicitly as above. Reread the Charts paragraph of the current
main-20261015 blueprint: the counit must be the integral sum/ordered integration
counit, and scalar comparison must use the canonical tensor/pullback isomorphism.
A bare geometric isomorphism did not enforce this. The normalization equation
now enforces the canonical composite, and theta is on the geometric functor.
Reread the intrinsic-domain clause: all three intrinsic conjuncts occur directly,
with no circular theorem dependency. In dimension zero the tower normalization
is the unit/identity/shift-zero composite; empty schemes and the zero ring retain
the same functors and equations. No new node, statement correction or disputed
statement is needed. No second agent was started, as the dispatcher forbids it.


Additional repair searches: msearch leanfinder queried "Canonical derived comparison
pullback commutes with twisted shifted affine chart inverse image with its normalized
counit" (eight unrelated affine-cover or module-sheaf pullback hits, no chart map);
msearch loogle queried "AlgebraicGeometry.Etale.affineTraceRight, CategoryTheory.Iso"
(the project name is not indexed, zero hits); msearch grep queried
"affineTraceRight|chartGeometryComponent|etaleChartNormalComponent" (zero Mathlib hits).
Source rg found only the private `lineENormalForm`/`towerENormalForm` helpers and the
existence-only affine normal-form theorem. The public monoidal comparison is reused
from ComparisonMonoidal. The site/pullback interchange is composed inline from
mapDerivedCategoryCompIso, the existing comparisonUpperStarCompUpperStarIso and
mapDerivedCategoryNatIso, avoiding an otherwise unnecessary OpenCover import.
The citer `lem-sp-chart-counit-scalar-transport` was read in full: it uses the canonical
geometric tensor/pullback scalar map, which is exactly why the pinned normalization
and geometric counit in this repair are necessary.


The component definitions specialize the canonical natural comparisons at an input
before elaborating their concrete functor endpoints. This affects only elaboration;
`Datum.geometric` is still a natural isomorphism of whole derived functors and its
normalization equation holds at every input. No per-degree replacement or weakened
naturality assertion is used. The imported affine normal-form existence theorem's
private canonical helpers are not externally accessible; the delivery uses its
coordinate construction with public canonical tensor, shift and pullback maps.


Repair validation: the final module compiled through scompile.py in both contexts,
52.2 s for the sandbox module and 48.8 s for its library module. Both compiles
were clean apart from the expected admitted-theorem warning. The node differs
from the current live node only in its lean record; its signature was checked
verbatim against the source and all 21 owning declarations are listed. There
is exactly one postponed proof, the named item theorem. Temporary diagnostic
files were removed before delivery.

The repaired packet passed deliver2.py --no-push: dry-run commit d0fa1d747ba
passed server preflight and per-file compilation. A final docstring cleanup
replaced the obsolete incidental predicate name by its three intrinsic clauses;
the statement and all definitions are unchanged from the clean compile.
