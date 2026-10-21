## Worker report

The delivery states the comparison of the actual Kummer-normalized projective-line and
vector-bundle integration arrows. Definitions use real supported Cartier Kummer maps,
canonical comparison mates, exact extension by zero, K-flat tensor comparisons, and
ordered counit composition. The pro-etale vector integration is selected only from a
unique local normalization property; its object and map are determined by that property.

The item module has separate declarations for the projective decomposition and trace,
open counit, global trace, tensor projection/adjunction transpose, and exponent transition.
The supporting modules expose the independent pro-etale ordered integration. No arbitrary
map or primitive root is a parameter.

Hypotheses and clauses:

- `l`, `[Fact l.Prime]`, `E`, its field, Padic algebra, and finite-dimensional instances
  give the fixed prime and finite coefficient extension. `n : ℕ` is the predecessor of
  the positive coefficient level, so `finiteTateCoefficient l E n` is precisely the
  size lift of O_E/(varpi_E^(n+1)). Every positive level is covered.
- `S` and `[IsNoetherian S]` permit a statement more general than the finite-type base
  specialization: finite type over the fixed field supplies this instance. `hS` is
  invertibility of l, a consequence of the fixed field characteristic convention.
  No separatedness of S occurs.
- `d : ℕ`, the module sheaf `F`, and `IsFiniteLocallyFreeOfRank d` are the existing
  `VectorBundleZeroSection` bundle, its projection, and its zero section.
- `r : ℕ` indexes positive annihilating exponents by r+1; `hA` is exactly l^(r+1) A=0.
  No relation to n, ramification, or flatness of A over Z/l^(r+1) is required.
- `twistComparison` chooses the already uniquely root-normalized descent. `twistDerived`
  places it in degree zero and shifts. `exponentTransition` is the unique normalized
  root-power map; `baseExponentComparison` takes its ordered tensor powers.
- `projectiveChern` is the constant-to-supported-unit composite with `cartierKummerMap`.
  `projectiveH` is its actual adjoint. `projectiveU` is the actual shifted twisted unit.
  `projectiveB` is their biproduct desc; `projectiveB_isIso` supplies its inverse;
  `projectiveTrace` reuses `geoP1Trace` with that specific isomorphism.
- `projectiveComparison` states beta C(b_e)=b_p, trace beta=C(trace_e), and trace h=id.
  `openCounitComparison` is the full actual counit square, with the exact/left-derived
  coordinate isomorphisms inserted on both sides.
- `projectiveEpsilon` is the unique morphism fixed by the inverse-projection counit
  equation, hence inverse proper projection, tensor with the independent trace,
  and the canonical unit. `lineCounit` restricts it with the actual open counit.
  `towerCounit` is selected from the unique family satisfying the literal identity
  at zero and the ordered composite-counit successor equation. HEq only packages
  the defining successor identification of the published right tower. `towerSiteComparison`
  compares sources only and contains no ordinary trace. `localIntegration` prefixes
  the canonical inverse-frame exchange and Tate/compact-support comparisons.
- `VectorNormalization` quantifies every open and every frame. Unique gluing supplies
  `vectorIntegration`. The main equation is beta_pi followed by this actual map equal
  to C of `Etale.vectorBundleIntegration`.
- `vectorTensorComparison` quantifies ordinary bounded-constructible finite-Tor K.
  `pe.inv` and `pp.inv` are required to equal the actual projection maps (with the
  canonical twisted-source comparison, packaged by `comparedModuleProjection`). Its next conjunct is the projection square,
  then the integration square, then the `boundedSiteTranspose` equation with the
  canonical `boundedSiteRho`. The final IsIso is the ordinary purity adjunct. The new field
  `ordinary_normalization` requires a `VectorPurityGammaNormalized` family and identifies
  that very adjunct with its component after the canonical signed tensor symmetry.
  Its inverse therefore is the integration-normalized vector-bundle identification
  specified in the corollary, rather than an unspecified invertible arrow.
- `vectorExponentIndependence` is the global trace equation under the actual ordered
  root-power tensor transition. The corresponding tensor and transpose formulas use
  those same comparisons and therefore have the same exponent independence.

Dependencies used: `ProjectiveLineTrace.projectiveLineTraceDatum/Transport`,
`CartierKummerMap.cartierKummerMap`, `FiniteTateSiteDescent.finite_tate_site_descent`,
`GeoP1Cohomology.geoP1Comparison/geoP1PullComparison/geoP1UnitPullback/geoP1Trace`,
`VectorBundleIntegrationCharts.vectorIntegrationCoefficient/vectorIntegrationLocalTrace`,
`Targets.VectorBundlePurity.vectorBundlePurityCompactification/Adjunction/ProjectionMap`,
`CanonicalCompactSupportSiteComparison.compactSupportSiteComparison`,
`OpenProjectionSiteTransport.openProjectionExtensionComparison/openProjectionRestrictionComparison`,
and `BoundedSiteAdjunctionTranspose.boundedSiteTranspose/boundedSiteRho`.
The public generic derived Koszul symmetry is reused from `EtaleDerivedTensorSymmetry`.

Edge cases read through: rank zero is the literal identity tower, zero tensor power is
constant coefficients, the empty scheme has the unique maps, n+1 and r+1 cover all
positive indices, larger common exponent handles unordered pairs of annihilators,
ramified quotients need no divisibility, and a nonseparated base remains permitted.
The infinity divisor ideal is the coordinate principal ideal on its chart and the unit
ideal on the other chart, including over rings with zero divisors.

Searches: msearch LeanSearch, query `etale proetale site comparison vector bundle integration
Kummer trace`, returned 8 site/etale definitions, no normalized trace. LeanFinder query
`canonical comparison coordinates for finite Tate root tensor exponents, supported Kummer
projective line trace, ordered affine line integration and proetale vector bundle integration`
returned BDeRham/PreTilt/standard-etale signatures, no match. Loogle
`CategoryTheory.Adjunction, CategoryTheory.Iso` returned abstract adjunction transports.
Mathlib grep `Kummer|vectorBundleIntegration|affineTrace` in AlgebraicGeometry returned zero.
Project rg found ordinary integration and canonical generic comparison definitions, reused
here; its pro-etale trace system is ZMod-only and does not provide these all-A_E,n local
integration arrows. Blueprint searches for ordered integration, site coordinates, supported
projective and proetale vector integration found zero; tensor projection found three broader
blueprint statements, not these coordinate definitions. The matching generic comparison
owner `def-sp-p1-comparison-arrows` is cited, not restated as a rival construction.

No statement correction or statement dispute is proposed. The server compile wrapper is
used for every compile, each module separately; no local/global lake build was run.

## Second reading by NQ

The dispatcher explicitly forbids spawning other agents and assigns independent review to
the maintainer. This is a self second pass, not a claimed independent-agent review. It
checked the node against each declaration and the source formulas. In particular the
pro-etale trace is constructed from its supported Chern decomposition, then projected;
its vector integration uses independent pro-etale line counits. The site comparison in
local normalization only changes source coordinates and never defines the trace by the
desired equality. The coefficient level and annihilator use successor indexing explicitly.

## New nodes

The returned-head repair also adds three owners of exact unchanged published definitions:
`def-pur-open-site-comparison-arrows` (derived extension and restriction comparisons;
Stacks 09AF/099R), `def-pur-bounded-site-transpose-arrows` (Hom-chain transpose and rho;
Stacks 0B65), and `def-pur-vector-integration-adjunction-arrows` (the five ordinary
bundle integration coordinates; current blueprint integration-adjunct formula).
All three are `existing: true`; their specific statements, sources, prerequisite
lists, exact declarations, and actual search results are detailed below.

`def-pur-finite-site-coordinates`: canonical existing comparison coordinates, finite
root-projection descent, shifted twist, and root-power transition.

`def-pur-supported-projective-chern`: actual supported Chern arrow and its adjoint,
with the shifted twisted unit.

`def-pur-supported-projective-site-arrows`: biproduct decomposition and second-projection
trace with the actual supported Chern component.

`def-pur-finite-site-tensor-projection`: canonical tensorator, signed symmetry, constant
unitor, and coefficient-first projection coordinates.

`def-pur-proetale-projective-coefficient`: canonical projective tensor/pullback source
comparison, using the existing generic tensorator and geometric comparison.

`def-pur-proetale-projection-integration`: the proper projection is invertible and its
normalized projective counit is uniquely specified by the projection/trace/unitor equation.
The selected morphism is determined uniquely; its Hom type is named to keep kernel
checking small.

`def-pur-proetale-affine-line-counit`: actual open-extension restriction of the
projective counit and its canonical right-object comparison.

`def-pur-proetale-ordered-integration`: ordered counit tower,
canonical source comparison and inverse-frame local integrations.

`def-pur-proetale-frame-integration`: inverse-frame exchange and the local formula
using the ordered integration.

`def-pur-proetale-vector-integration`: unique gluing with that prescribed local formula,
and canonical compact-support comparison.

Each node is a definition needed by the item, sourced at the corresponding formulas of
the item and its current blueprint ancestor, with the searches recorded above.

`def-pur-proetale-vector-integration-arrows`: canonical tensor projection, twisted-source
comparison, and Hom types for integration, separated from the unique gluing definition.

`def-pur-vector-tensor-site-equations`: the literal tensor projection, integration, and
adjunction comparison equations, in a separate module to stay within the compile limit.
The auxiliary `ae` and `ap` binders are fixed by HEq to the displayed inverse-projection,
tensor-trace and unitor formulas; they add no choices or assumptions.

Recorded dependency interfaces (module and full declaration):

- `def-pur-conventions`: `Sheaf.Paper.PurityFiniteSetting`, `WeilConjectures.PurityFiniteSetting`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-asd-vector-bundle-zero-section`: `Sheaf.AlgebraicGeometry.VectorBundleZeroSection`, `AlgebraicGeometry.VectorBundleZeroSection.scheme`.
- `def-sf-comparison-derived-pullback`: `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`, `AlgebraicGeometry.ProEtale.siteComparisonDerivedPullbackPlus`.
- `def-weil-exceptional-inverse-image`: `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`, `WeilConjectures.ConstructibleExceptionalCoefficients.System`.
- `lem-asd-etale-finite-twist-pullback`: `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`, `AlgebraicGeometry.Scheme.etaleFiniteTwistPullback`.
- `def-coefficient-twists-detailed`: `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`, `WeilConjectures.sfQbarTwistingFunctor`.
- `lem-amb-cartier-kummer-map`: `Sheaf.AlgebraicGeometry.CartierKummerMap`, `AlgebraicGeometry.Etale.cartier_kummer_map`.
- `def-amb-p1-trace`: `Sheaf.AlgebraicGeometry.ProjectiveLineTrace`, `AlgebraicGeometry.Etale.projectiveLineTrace`.
- `lem-weil-pbc-comparison-direct-image-canonical-mate`: `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`, `AlgebraicGeometry.ProEtale.fixedComparisonDirectImageMatePlus`.
- `def-amb-vector-integration`: `Sheaf.AlgebraicGeometry.VectorBundleIntegration`, `AlgebraicGeometry.Etale.vectorBundleIntegration`.
- `lem-amb-affine-space-top-trace`: `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace`, `AlgebraicGeometry.Etale.exists_affineSpaceTopTrace`.
- `cor-pur-vector-bundle-purity`: `Sheaf.Paper.VectorBundlePurity`, `WeilConjectures.PurityFiniteSetting.vectorBundlePurity`.
- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`, `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology`.
- `def-amb-etale-compact-support`: `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`.
- `def-compact-support-direct-image-detailed`: `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`, `AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport`.
- `def-weil-derived-pullback-tensor-hom`: `Sheaf.Paper.DerivedPullbackTensorHom`, `WeilConjectures.commonStageDerivedInternalHom_existsUnique`.
- `lem-cbc-proetale-extension-zero-comparison`: `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`, `AlgebraicGeometry.ProEtale.openImmersionLowerShriekComparison_coherence`.
- `def-weil-finite-tor-amplitude`: `Sheaf.Paper.FiniteTorAmplitudeSites`, `WeilConjectures.finiteTorConstructibleEtale`.
- `lem-amb-finite-tate-site-descent`: `Sheaf.Paper.FiniteTateSiteDescent`, `AlgebraicGeometry.Scheme.finite_tate_site_descent`.
- `def-sp-p1-comparison-arrows`: `Sheaf.AlgebraicGeometry.GeoP1Cohomology`, `AlgebraicGeometry.ProEtale.geoP1Comparison`.
- `lem-kun-tensor-sym`: `Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry`, `AlgebraicGeometry.Etale.derivedTensorSymmetry`.
- `def-pur-vector-purity-normalization`: `Sheaf.Paper.VectorPurityNormalization`, `WeilConjectures.PurityFiniteSetting.VectorPurityFunctorConclusion`.
- `def-pur-open-site-comparison-arrows`: `Sheaf.AlgebraicGeometry.OpenProjectionSiteTransport`,
  `AlgebraicGeometry.ProEtale.openProjectionExtensionComparison/openProjectionRestrictionComparison`.
- `def-pur-bounded-site-transpose-arrows`: `Sheaf.Paper.BoundedSiteAdjunctionTranspose`,
  `AlgebraicGeometry.ProEtale.boundedSiteTranspose/boundedSiteRho`.
- `def-sf-compact-support-site-comparison-construction`:
  `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`,
  `AlgebraicGeometry.ProEtale.compactSupportSiteComparison`.

The tensor equations are stored in `TensorCompatibilityData` over a general finite
ring, then specialized by `TensorCompatibility` to the specified finite coefficient
ring, actual normalized pro-etale trace, and canonical site isomorphism. Its fields
`ordinary_formula`, `pro_formula`, `ordinary_projection`, `pro_projection`,
`projection_square`, `integration_square`, `transpose_square`, and `ordinary_purity`
are respectively the inverse-projection formulas, canonical projection arrows,
projection square, integration square, transpose equation, and invertibility clause.
The further field `ordinary_normalization` identifies this same adjunct with the
independently normalized `VectorPurityGamma` of the corollary; the source swap is the
existing `Etale.derivedTensorSymmetry`, and its target is the same Brown right adjoint.
`Nonempty` here asserts existence of these constrained witnesses; no definition
selects an arbitrary trace from it. Heterogeneous equality packages equality of the
same arrows in the explicitly displayed source coordinates.


## Ownership repair details

`def-pur-open-site-comparison-arrows` owns exactly the existing definitions
`AlgebraicGeometry.ProEtale.openProjectionExtensionComparison` and
`AlgebraicGeometry.ProEtale.openProjectionRestrictionComparison` in
`Sheaf.AlgebraicGeometry.OpenProjectionSiteTransport`. Its source is Stacks 09AF
(the adjoint-normalized extension comparison) and 099R (inverse image). No Lean
module is added: `existing: true` records the unchanged published constructions.

`def-pur-bounded-site-transpose-arrows` owns the existing `boundedSiteTranspose`
and `boundedSiteRho` in `Sheaf.Paper.BoundedSiteAdjunctionTranspose`. It specifies
exactly the Hom chain and unit formula, with arbitrary finite A, compactification,
ordinary right adjoint H, and its actual adjunction. Its source is Stacks 0B65,
with the already owned canonical compact-support comparison. It asserts no
boundedness or invertibility theorem and adds no module.

`def-pur-vector-integration-adjunction-arrows` owns the five unchanged definitions
`AlgebraicGeometry.Etale.vectorBundlePurityCompactification`,
`vectorBundlePurityLower`, `vectorBundlePurityAdjunction`,
`vectorBundlePurityTwistedPullback`, and `vectorBundlePurityProjectionMap` in
`Sheaf.Targets.VectorBundlePurity`. Its source is the integration-adjunct formula
of current blueprint `thm-amb-vector-bundle-purity`; it records the published
Nagata coordinate model, ordinary Brown adjunction, and actual signed projection.
It is a definition node, not an assertion of vector purity, and adds no module.

The three new owners have small, specific prerequisite lists. For all three the
logged LeanSearch and LeanFinder query was `canonical derived etale proetale open
extension restriction comparison, bounded adjunction transpose and vector bundle
compact support adjunction`: each returned eight generic restriction, sheaf
adjunction, or condensed-module signatures, none the required definitions.
Mathlib grep `openProjectionExtensionComparison|boundedSiteTranspose|vectorBundlePurityCompactification`
in AlgebraicGeometry returned zero hits. Direct source rg found no upstream
WeilConjectures names and located the exact existing Sheaf definitions at the
lines recorded in the nodes. The DAG search found only theorem-module helper
records, with no definition owners. Blueprint searches `open projection`,
`bounded site transpose`, and `vector bundle purity` each returned zero matches.
The new nodes retain the actual logged search results, rather than copying the
item's broad source or its boilerplate prerequisites.

## Repair of immutable head 7845f3f7f26a

The retained packet first passed `deliver2.py --no-push` as a72ba732ef0. This
mechanical pass did not repair the independent semantic return; the changes below
are substantive deltas from the returned packet, on top of the current live base.

F1 (H2/H12): added the two definition owners for open and bounded-transpose
arrows and cited them from the item and all retained new nodes. Replaced the
statement-only uses of `lem-pur-compact-support-site-coherence` by its actual
construction owner `def-sf-compact-support-site-comparison-construction`.
The source modules and their canonical maps are unchanged. The three original
stage-1 proof prerequisites remain in `proof_deps` as proof tools.

F2 (H2): added and cited `def-pur-vector-integration-adjunction-arrows` for all
five plain definitions actually used from `Sheaf.Targets.VectorBundlePurity`.
No new purity assumption or copied definition was introduced.

F3 (H3): `TensorCompatibilityData.ordinary_normalization` now asserts existence
of the independent `VectorPurityGamma` satisfying `VectorPurityGammaNormalized`,
and equality of its K component with the very adjunct of `ae` already occurring
in `transpose_square` and `ordinary_purity`, after the canonical tensor swap.
The displayed equality uses `HEq` solely for the two published presentations of
the derived tensor functor. Its right side is explicitly the signed symmetry
followed by `γ.app K`; there is no arbitrary source identification. Together with
`ordinary_purity`, this pins the inverse to the same integration-normalized purity
identification as `cor-pur-vector-bundle-purity`. That corollary remains the named
source of this family, and `def-pur-vector-purity-normalization` is now directly
used in the statement. The item's mathematical text has not changed.

## Second reading by NQ (repair self-check)

This is a self-check because the dispatcher forbids other agents; the maintainer
supplies the independent review. Opened the item, tensor module, all three new
owner records, and their exact published declarations and docstrings. F1/F2
records introduce no duplicate Lean definitions; their signatures and modules
point to the unchanged sources. Their statements give the actual formulas,
not generic existence or an assumed comparison. The compact-support inverse
orientation B agrees with `compactSupportSiteComparison.inv`.

For F3, read `VectorPurityGamma` and `VectorPurityGammaNormalized`: the former has
source W tensor pi-star K, while the item uses pi-star K tensor W. The explicit
`Etale.derivedTensorSymmetry` swaps precisely those factors. The target in both
is the same ordinary Brown right adjoint computed from the integration's Nagata
compactification. `ordinary_normalization` existentially concludes the normalized
family and its component equation, adding no hypothesis to the theorem. The
existing `ordinary_formula` still fixes ae by inverse projection, actual trace
and right unitor. Thus the transpose comparison uses the adjunct of that exact
normalized integration, and its inverse is the named purity identification.
The rank-zero, empty-scheme and zero-coefficient-object cases are retained:
the twist is the unit at rank zero, the symmetry is canonical at units/zero,
and there is no nonempty or positive-rank assumption. The unchanged local
pro-etale integration, supported Kummer generator, exponent independence,
finite-Tor range, and arbitrary nonseparated finite-type base remain as checked
above. No statement correction, hollow data, or extra axiom was introduced.


Validation after the repair: `scompile.py NQ lem-pur-vector-integration-site-comparison`
compiled all 13 delivered modules separately in dependency order against the live
published build, including `VectorTensorSiteEquations` and its consumer
`VectorIntegrationSiteComparison`; exit 0 with no errors or unexpected warnings.
The server also checked each private overlay and canonical library module name.


The repaired dry run's first metadata pass caught the `noncomputable` prefix in
an existing-definition signature and the location of the new-node names outside
the exact report section. Both are repaired: the signature starts at `def` as the
server parser expects, and the exact `## New nodes` section names all owners.
