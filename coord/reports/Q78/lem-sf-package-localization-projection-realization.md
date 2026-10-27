## Worker report

The delivery states lem-sf-package-localization-projection-realization in
Sheaf.Paper.SfPackageLocalizationProjectionRealization. Every theorem has proof
`by sorry`; the helper definitions have explicit data. There is no statement
correction or independent new notion. This repairs returned delivery 47e2b3d69259.

The current source read was
literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md,
clauses (3) and (5), together with the complete DAG statement and seven proof steps.
The stage-1 repair note is resolved, names stage 1, and requires preserving the
accepted re-split; this delivery changes only lean. The illustrative CompactObject
Sheaf module has now been withdrawn, and its node correctly points upstream.

Hypotheses and clauses:

- The finite field and its algebraic closure are `D : FiniteFieldDatum.{u}`.
  `C : D.CoefficientDatum` supplies the prime, `C.different`, and coefficient closure.
  E, Field, Algebra (Padic C.l), FiniteDimensional, n, hn encode the finite extension
  and positive coefficient exponent. The valuation ring, uniformizer and finite
  quotients are exactly those inside the imported operation datum and categories.
- `S : SixFunctorOperationDatum D C E n hn` is the recorded operation datum, with
  its normalized finite, completed integral, rational and common-stage operations.
  No arbitrary compact-support map or coefficient functor is supplied instead.
- Z,U,X,Y are `SixFunctorSpace D`: finite-type schemes over D.k. Their structure
  maps have IsSeparated. Morphisms are in that over category; f has IsSeparated,
  LocallyOfFiniteType and QuasiCompact. `i` is closed, `hj` is open, and every
  localization theorem explicitly binds `_hij` as the complementary range equation.
  Named section instances are explicitly included, so even hypotheses not required
  for typing remain theorem parameters.
- The finite input domain is `S.finiteTorDomain X`; the ambient category for finite
  distinguishedness is the ordinary uncompleted intrinsic pro-etale derived category.
  The other stages are exactly sfIntegralConstructibleCategory,
  sfRationalConstructibleCategory and generalAlgebraicallyClosedConstructibleCategory.
  In particular integral completeness and one interval uniform in n are inherited
  from sfIntegralConstructible, not replaced by a levelwise boundedness condition.
- `sfPackageLocalizationOpenComparison` composes the prescribed support compositor
  with openIdentification. `sfPackageLocalizationClosedComparison` uses the same
  compositor and properIdentity. Their directions identify the actual R(fj)!j* and
  R(fi)!i* values with Rf! applied to the source recollement vertices.
- `sfPackageLocalizationFirst` is that open comparison followed by Rf! of the
  open-adjunction counit. `sfPackageLocalizationSecond` is Rf! of the closed unit
  followed by the inverse closed comparison. `sfPackageLocalizationTriangle` uses
  exactly these two arrows, with no unconstrained first or second arrow.
- `SfPackageLocalizationBoundary` is a natural transformation from the actual
  third-vertex functor to the actual first-vertex functor shifted by one.
  Its naturality gives the third triangle square for every input morphism. The
  four conjuncts of sfPackageLocalizationProjectionRealization assert distinguished
  triangles on precisely the stated input domains at all four stages.
- `SfPackageLocalizationRealizes` requires existence of the specified source
  recollement boundary and, for every distinguished completion of the prescribed
  source counit/unit, equality of the actual boundary with its image and shift,
  conjugated by the canonical outer comparisons. sfPackageLocalizationFiniteImage
  specializes this to sixFunctorFiniteSupport and S.finiteSupport and states the
  finite Tor condition on all three output vertices.
- `sfPackageLocalizationIntegralTower` fixes one c and one tower whose tower field
  is the designated exists_compactSupportReductionTower choice. Its datatype retains
  evaluation isomorphisms and EVERY quotient-induced transition m to n, the total
  right-derived inverse-limit universal property and K-injective projection
  normalization. It asserts triangulated tower and limit shifts, one natural
  comparison e with the actual support functor, and projection normalization against
  the defining Roos vertex. The map equation identifies actual support maps with
  total limits of whole strict tower maps. The shift equation identifies the
  composite shift. SfPackageLocalizationRealizes then fixes the boundary itself,
  rather than recovering it from unrelated finite evaluations.
- `sfPackageLocalizationRationalization` states the whole triangle over the raw
  rationalized category and the actual boundary square through S.higher.rationalization.
  `sfPackageLocalizationCommonStages` asserts existence of one field system: every
  finite-field boundary rationalizes a tower-pinned integral boundary, and that same
  family is used for all commonStageComparison and coefficientTransition squares.
  `SfPackageLocalizationFieldSystem` uses one family for every E0 <= L, including
  equality and repeated stages, with the prescribed coefficientTransition and its
  normalized exact scalar shift. The first two squares follow from the recorded comparison's
  unit/counit and composition equations; the third square is explicit.
- `sfPackageLocalizationWeil_rational` and `_common` take actual finite-field models,
  geometric base-change maps, and the recorded sfWeilComplex/sfCommonStageWeilComplex
  fixed pairs. The middle Weil isomorphism uses the actual compact-support Frobenius
  exchange followed by support of K.str. The outer isomorphisms use pullback exchange
  followed by the actual compact-support exchange for fj or fi. All three commuting
  equations, including the Frobenius shift on the boundary, are explicit in
  SfPackageLocalizationWeilTriangle. The geometric open/proper witnesses are implied
  by base-change stability; their explicit binders let the consumer install them
  without adding a mathematical restriction.
- The projection conjuncts use CompactSupportFiniteProjection.Laws and
  CompactSupportProjectionLaws for the exact canonical mates. These assert IsIso,
  naturality in both inputs, compactification, composition and proper coincidence.
  The finite second input alone has finite Tor, the first remains bounded
  constructible. Integrally the second predicate is integralFiniteTorDomain;
  at fields every bounded constructible input has finite Tor. The datum fixes
  integralTensor and pullback as the completed operations.
- sfPackageProjectionCoefficientCompatibility gives the actual canonical
  CompactSupportProjectionChange square for all positive quotient reductions,
  integral reductions, finite scalar inclusions and ramified finite changes, on
  exactly the published bounded comparison domains. The general projection laws
  still retain arbitrary bounded constructible first inputs.

Dependency declarations read and used:

- def-fix-six-functor-datum: Sheaf.Paper.SixFunctorOperationDatum,
  WeilConjectures.SixFunctorOperationDatum and its finiteTorDomain,
  integralFiniteTorDomain; also the owning SixFunctorOperationDatumStages interfaces
  SixFunctorPushStage, SixFunctorCoefficientComparison and normalization fields.
- def-weil-open-closed-recollement:
  Sheaf.AlgebraicGeometry.FiniteOpenClosedRecollement,
  AlgebraicGeometry.Scheme.FiniteOpenClosedRecollementTriangle and
  finiteRecollementDerivedAdjunction. The finite realization uses exactly the
  normalized open counit and closed unit from this node, through the operation datum.
- def-weil-weil-sheaf-complex: Sheaf.Paper.SfWeilSheafComplex,
  WeilConjectures.sfWeilComplex, sfCommonStageWeilComplex and their actual geometric
  Frobenius functors; these are fixed pairs, not derived categories of Weil sheaves.
- def-exchange-projection: Sheaf.Paper.ExchangeProjectionSuppliedDomains,
  CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage.projection;
  used via SixFunctorExchangeData and the canonical projection-law interfaces.
- Proof modules are imported for every recorded proof dependency. The finite
  triangulated candidate is sfIntrinsicCompactSupport; the strict-tower comparison
  uses exists_compactSupportReductionTower and CompactSupportReductionTowerConstruction;
  the source recollement is sfOpenClosedTriangle_finite/integral_rational/qbar;
  the reduction boundary is sfRecollementReductionBoundary; total realization is
  sfCompactSupportTotalLimitRealization. Projection uses compactSupportProjectionFormula
  and compactSupportProjectionFormula_coefficients. Mathlib's Triangle, Pretriangulated,
  shiftFunctor and Functor.CommShift are the exact triangulated-category notions.

Edge cases checked before and during writing: U empty or Z empty is never excluded
by a Nonempty or support condition; n=1 is included and tower index m=0 means
exponent one. Zero input has the same actual functor maps. Identity finite field
inclusions are included by E0 <= L. Arbitrary scheme/site universe u is retained;
the intrinsic small pro-etale site keeps its existing object/morphism sizes.
Weil input structure is arbitrary K.str and is not required to lift integrally.
All helper category and object universes are declared explicitly, with autoImplicit
and relaxedAutoImplicit false. Failed #synth probes were removed.

Searches made using the prescribed msearch.py:

- leanfinder: “Compact support localization distinguished triangle strict reduction
  tower total derived inverse limit projection formula”: eight generic derived
  fractions/degree-bound hits; none states the item.
- loogle: “CategoryTheory.Functor.IsTriangulated”: twelve general triangulated-functor
  results; no compact-support localization or coefficient tower realization.
- grep: “recollement|projectionFormula|projection_formula|strictTower”: zero Mathlib hits.
- leansearch: “Compactly supported image of open closed recollement triangle, strict
  coefficient towers and derived limit, and canonical projection formula”: eight
  generic truncation, exactness and limit results; no match.
- rg of lean/WeilConjectures and lean/Sheaf for the item, localization, recollement,
  projectionFormula and the proposed declaration names: ordinary localization,
  finite recollement, existing normalized tower and projection components are present,
  but no theorem assembles this statement. Those components are reused. A literal
  grep of the item id in lean/WeilConjectures returned no hit. The upstream-name
  inventory has no collision with the declarations added here.

No mathematical STATEMENT-DISPUTED remains. The two returned H3 encoding faults
are repaired as detailed below. Every helper is part of this node's
actual arrows or its conclusion predicates, not a replacement six-functor notion.
The full node statement is represented by the declarations listed in lean.declarations.

## Second reading by Q78

The dispatcher expressly forbids starting another agent; independent maintainer
review is the next stage. This is a self-check, not a claim of independent review.
Reopened the node and repaired source and traced the displayed endpoints and every
hypothesis. The maintainer return disproved the prior self-check of field-boundary
coherence and operation-comparison canonicality; both have been replaced below. A first draft omitted the explicit boundary transport and coefficient
squares; these were added as FiniteImage, IntegralTower, Rationalization, CommonStages
and the single FieldSystem. A further check found that arbitrary outer Weil isomorphisms
would not state the canonical Weil assertion; the final version constructs them
from the actual pullback and support Frobenius comparisons. All theorem proofs
remain sorry, helper data are actual compositions, and the closed-unit/open-counit
orientations match the node. Only lean and the permitted added definition stmt_deps are changed.

Elaboration check: the common-stage clauses use the published
`sixFunctorCoefficientRational` interface, definitionally the same finite rational
stage, to avoid expanding its coefficient-model category during inference.
Temporary profiler options are removed from the delivered source.

## Returned delivery repaired

The return at immutable head 47e2b3d69259 identified two H3 defects.

1. **Boundary coherence across coefficients and Weil structures.**
   `SfPackageLocalizationTowerBoundary H hl δI` retains the complete strict-tower
   assertion from IntegralTower, including the normalized comparison, all projection
   equations, map equation, composite shift, and `SfPackageLocalizationRealizes`.
   It additionally equates the ambient boundary with the image of this *same* δI
   under the fully faithful integral inclusion and its prescribed shift. Thus δI
   cannot be changed to an unrelated distinguished completion after compact support.
   `sfPackageLocalizationRationalization` now takes any δI satisfying that predicate
   and asserts its coefficient square with δR, using the canonical rationalization
   shift. `SfPackageLocalizationRationalBoundary` records exactly this tower origin.
   `sfPackageLocalizationCommonStages` asserts ONE family δE and ONE δbar, together
   with `SfPackageLocalizationFieldSystem`. Every δE is tower-pinned via its own
   integral coefficient field. The identical δE appears in all exact inclusion and
   scalar-transition squares. The separate ScalarTransitions theorem and its
   independent existential family have been removed. The rational and common Weil
   theorems take these pinned boundaries as arguments rather than choosing a new δ.
   This blocks the return's A¹/{0} rescaling: 2δ must satisfy the fixed tower image
   and the actual coefficient square, not only a distinguishedness condition.

2. **Canonical operation comparisons in the Weil equations.**
   The existential e/ej/ei binders have been removed. RationalPullComparison and
   CommonPullComparison are eqToIso of the datum's literal pullback normalization.
   SupportAdjointComparison first uses the datum's compactification comparison and
   `sixFunctorFactoredSupportIdentification`, then the unique-adjoint isomorphisms
   preserving the specified open and proper adjunctions. RationalSupportComparison
   and CommonSupportComparison specialize this construction to the actual base change
   of the model compactification. OuterComparison is their whiskered composite with
   the literal pullback comparison and the base-change composition equality.
   The Weil equations use these defined comparisons verbatim. No choice from
   `fieldWeilShriek_recorded` or a mere Nonempty comparison is used.

The three landed definition owners newly used by these canonical constructions are
added to stmt_deps: def-zl-field-weil-shriek-shift-data,
def-zl-common-stage-weil-shriek, and def-zl-frobenius-compact-support-comparison.
Their recorded modules, complete relevant definitions and normalization docstrings
were read. The source remains the current blueprint clause (3); the first two
arrows, input domains, empty-stratum cases and projection clauses are preserved.
The sandbox was compared with the current node: its mathematical fields agree
with the returned version; only the Lean record and these permitted added definition
dependencies are changed. Delivery wrappers rebase onto the current live branch.

The two new elementary helper statements about the geometric base-change functor
retain named sorry proofs and source/proof docstrings under this node. All comparison
definitions themselves contain real data.

Repair validation: the exact delivered module passes scompile.py in both sandbox
and library modes with no warnings. The canonical-comparison helper probe also
passes. All 10 theorem proofs remain named sorry proofs; every definition contains
real data. The node signature is copied verbatim and all Lean lines are at most
100 characters.
