## Worker report

The module states integrationExponentTransposeTransport; its only postponed proof is
that named theorem. All helpers contain real constructions or explicit predicates;
there is no new site, coefficient, Tate twist, compact-support functor or integration.
The node's statement, dependencies and accepted proof are unchanged. The theorem
carries all twelve accepted proof steps verbatim in its docstring.

Hypothesis and clause correspondence:

- Fixed finite-field and coefficient data: `P : PurityFiniteSetting.{u}`. Its
  positive level is used as `P.level - 1` in the existing n+1-indexed finite
  coefficient interface, so its ring is O_E/(varpi^P.level), including level 1.
- Finite type S over k: `aS`, `[LocallyOfFiniteType aS]`, `[QuasiCompact aS]`.
  No separatedness over k is assumed. Noetherianity is derived in the conclusion
  definition by `isNoetherian_of_locallyOfFiniteType aS`; invertibility of ell is
  concluded as `hS`, rather than added as a hypothesis.
- Vector bundle rank d: `d : ℕ`, `F : S.Modules`,
  `[F.IsFiniteLocallyFreeOfRank d]`, with total space and projection exactly
  `VectorBundleZeroSection.scheme` and `.π`.
- Positive annihilating exponents: predecessors `r s : ℕ`, `hrs : r ≤ s`, and
  `hr hs` stating that ell^(r+1), ell^(s+1) kill the actual coefficient ring.
  Taking s=r includes the one-exponent conclusions at every exponent.
- Ordinary constant module categories and the small pro-etale site are the
  recorded `Etale.DerivedCategoryModule` and `DerivedCategory (Sheaf
  (Scheme.ProEt.topology _) (ModuleCat.{u+1} A))`. The ordinary and pro-etale
  object and morphism universes are retained; no universe equality is imposed.
- Root-normalized comparisons and tensor powers: the published
  `exponentTransition`, `baseExponentComparison`, and exact comparison functor;
  `integrationLineTransition`, `integrationVectorTransition`,
  `integrationTensorTransition`, `integrationTowerTransition` only apply the
  existing single, shift, tensor and pullback functors to those canonical maps.
- Compact support and B: the actual `vectorBundlePurityCompactification`,
  `vectorBundlePurityLower`, `rightDerivedLowerShriekOfCompactification`, and
  `vectorSite`. The inverse of `vectorSite` is precisely the stated B, built
  from the proper counit mate and adjoint extension comparison.
- Independent pro-etale trace: the published `vectorIntegration` constructed
  by degree-zero gluing of `localIntegration` and `orderedIntegration`.
  `IntegrationTraceComparison` is exactly the assumed actual-map equality at
  every killing exponent, with `vectorSite.inv` preceding that trace.
- K in D^b_ctf: the concluding quantifier uses
  `Etale.DerivedCategory.constructibleFiniteTor` on the actual finite coefficient.
- J and the canonical inverse projection arrows: `vectorTwisted` and
  `TensorCompatibilityData`. The latter retains `pe`, `pp`, `ae`, `ap`,
  `ordinary_formula`, `pro_formula`, `ordinary_projection`, `pro_projection`,
  `projection_square`, `integration_square`, `transpose_square`,
  `ordinary_purity`, and `ordinary_normalization`. Its defining projection maps
  and coefficient-first conventions are used unchanged, not privately copied.
- Normalized transpose, invertibility and inverse: `IntegrationTransposeData`
  contains isomorphisms `etaE`, `rho`, `etaP`, each with equality of its hom to
  the recorded adjunct, comparison-unit map or bounded-site transpose.
  `transpose` is the displayed comparison equation; `inverse` is the actual
  inverse equality `rho.inv ≫ comparison.map etaE.inv`. `right_plus` records the
  etale exceptional object's bounded-below witness; the twisted source's witness
  is `data.hM`. No unbounded pro-etale adjunction is introduced.
- Projective unit-Chern decompositions and inverse traces:
  `IntegrationProjectiveEquations` applies `IntegrationDecompositionEquations`
  to the ordinary datum and to isomorphisms whose homs are constrained to the
  supported `projectiveB` maps. It explicitly requires both the forward square
  and its inverse square, followed by second projection. Those second projections
  are the definitions of the actual traces, not arbitrary trace maps.
- Open restrictions: first two clauses of `IntegrationAffineEquations` use the
  actual `kummerTraceEtaleAffine` and `kummerTraceProAffine`, and map the root
  transition through restriction, extension by zero and proper direct image.
- All ordered affine traces: last clause of `IntegrationAffineEquations` is
  quantified over every tower length d; its two equations are the ordinary
  composite-adjunction counit and the independent pro-etale orderedIntegration.
  `integrationTowerTransition` uses the canonical coefficient descents in both
  directions and the root transition between them.
- Glued vector traces: `IntegrationVectorEquations` contains separate equations
  for the actual ordinary and independent pro-etale global traces.
- Coefficient maps, transposes and inverse purity at both exponents:
  `IntegrationTensorTransitionEquations.compatible` requires two fully normalized
  `IntegrationTransposeData` witnesses. Its six equalities cover ae, ap, etaE,
  etaP, etaE.inv and etaP.inv under the prescribed `integrationTensorTransition`.
  The canonical rho has no exponent parameter, so every comparison has the same
  right boundary at both exponents.

Dependency declarations read and reused (module — owning declaration):

- `cor-pur-vector-bundle-purity`: `Sheaf.Paper.VectorBundlePurity` — `WeilConjectures.PurityFiniteSetting.vectorBundlePurity`.
- `def-amb-etale-compact-support`: `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek` — `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`.
- `def-amb-vector-integration`: `Sheaf.AlgebraicGeometry.VectorBundleIntegration` — `AlgebraicGeometry.Etale.vectorBundleIntegration`.
- `def-asd-vector-bundle-zero-section`: `Sheaf.AlgebraicGeometry.VectorBundleZeroSection` — `AlgebraicGeometry.VectorBundleZeroSection.scheme`.
- `def-coefficient-twists-detailed`: `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted` — `WeilConjectures.sfQbarTwistingFunctor`.
- `def-compact-support-direct-image-detailed`: `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport` — `AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport`.
- `def-exchange-projection`: `Sheaf.Paper.ExchangeProjectionSuppliedDomains` — `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`.
- `def-kun-projection-formula-map`: `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection` — `AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`.
- `def-pur-conventions`: `Sheaf.Paper.PurityFiniteSetting` — `WeilConjectures.PurityFiniteSetting`.
- `def-sf-comparison-derived-pullback`: `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed` — `AlgebraicGeometry.ProEtale.siteComparisonDerivedPullbackPlus`.
- `def-weil-derived-pullback-tensor-hom`: `Sheaf.Paper.DerivedPullbackTensorHom` — `WeilConjectures.commonStageDerivedInternalHom_existsUnique`.
- `def-weil-exceptional-inverse-image`: `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` — `WeilConjectures.ConstructibleExceptionalCoefficients.System`.
- `def-weil-finite-tor-amplitude`: `Sheaf.Paper.FiniteTorAmplitudeSites` — `WeilConjectures.finiteTorConstructibleEtale`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` — `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories` — `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology`.
- `def-weil-pbc-proetale-modules`: `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules` — `AlgebraicGeometry.ProEtale.FiniteCoefficientModules`.
- `lem-amb-finite-tate-site-descent`: `Sheaf.Paper.FiniteTateSiteDescent` — `AlgebraicGeometry.Scheme.finite_tate_site_descent`.
- `lem-cbc-proetale-extension-zero-comparison`: `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison` — `AlgebraicGeometry.ProEtale.openImmersionLowerShriekComparison_coherence`.
- `lem-weil-pbc-comparison-direct-image-canonical-mate`: `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate` — `AlgebraicGeometry.ProEtale.fixedComparisonDirectImageMatePlus`.
- `thm-amb-etale-exceptional-adjoint`: `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint` — `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification`.
- `thm-amb-vector-bundle-purity`: `Sheaf.Targets.VectorBundlePurity` — `AlgebraicGeometry.Etale.vectorBundlePurity`.
- `thm-sf-ambient-adjoint-class`: `Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom` — `AlgebraicGeometry.ProEtale.specifiedExceptionalHomEquiv`.
- `def-pur-finite-site-coordinates`: `Sheaf.Paper.FiniteSiteCoordinates` — `AlgebraicGeometry.ProEtale.VectorIntegrationSite.twistComparison`.
- `def-pur-supported-projective-site-arrows`: `Sheaf.Paper.ProEtaleProjectiveLineTrace` — `AlgebraicGeometry.ProEtale.VectorIntegrationSite.projectiveTrace`.
- `def-pur-proetale-ordered-integration`: `Sheaf.Paper.ProEtaleOrderedIntegration` — `AlgebraicGeometry.ProEtale.VectorIntegrationSite.orderedIntegration`.
- `def-pur-proetale-frame-integration`: `Sheaf.Paper.ProEtaleFrameIntegration` — `AlgebraicGeometry.ProEtale.VectorIntegrationSite.localIntegration`.
- `def-pur-proetale-vector-integration`: `Sheaf.Paper.ProEtaleVectorIntegration` — `AlgebraicGeometry.ProEtale.VectorIntegrationSite.vectorIntegration`.
- `def-pur-vector-integration-adjunction-arrows`: `Sheaf.Targets.VectorBundlePurity` — `AlgebraicGeometry.Etale.vectorBundlePurityCompactification`.
- `def-pur-proetale-vector-integration-arrows`: `Sheaf.Paper.ProEtaleVectorIntegrationArrows` — `AlgebraicGeometry.ProEtale.VectorIntegrationSite.vectorProjection`.
- `def-pur-finite-site-tensor-projection`: `Sheaf.Paper.FiniteSiteTensorProjection` — `AlgebraicGeometry.ProEtale.VectorIntegrationSite.projection`.
- `def-pur-bounded-site-transpose-arrows`: `Sheaf.Paper.BoundedSiteAdjunctionTranspose` — `AlgebraicGeometry.ProEtale.boundedSiteTranspose`.
- `def-pur-vector-tensor-site-equations`: `Sheaf.Paper.VectorTensorSiteEquations` — `AlgebraicGeometry.ProEtale.VectorIntegrationSite.TensorCompatibility`.
- `def-pur-vector-purity-normalization`: `Sheaf.Paper.VectorPurityNormalization` — `WeilConjectures.PurityFiniteSetting.VectorPurityFunctorConclusion`.

The recorded broader coefficient systems are imported for the DAG's statement
vocabulary; the finite-stage arrows are the concrete interfaces recorded on the
finite-site, tensor-equation and vector-integration dependency nodes. Proof-only
imports follow the accepted split; lem-pur-affine-tower-integration-site-transport
has no published Lean record and therefore has no import yet.

Edge cases checked: d=0 is admitted by ℕ, with the existing zero-fold tensor and
identity tower. Empty S is admitted and all constructions are functorial on its
zero sheaves. s=r uses the canonical identity root transition; level 1 is retained.
No ramification divisibility or flatness over Z/ell^r is present. A nonseparated
finite-type base is admitted: only its structural map's finite-type conditions
appear. Zero K is included. K has an ordinary bounded-below witness and the ordinary
exceptional target has its own witness in IntegrationTransposeData.

Searches made:

- msearch.py leanfinder: “Change of annihilating exponent preserves Tate twists
  Kummer trace vector bundle integration projection and adjunction transpose”.
  Eight hits in algebraic trace, Hilbert 90, Picard and cotangent theory; no match.
- msearch.py loogle: “CategoryTheory.Adjunction.homEquiv,
  CategoryTheory.Functor.mapIso”: zero hits.
- msearch.py grep: “exponent.*[Ii]ntegration|[Ii]ntegration.*exponent”: zero hits.
- rg of WeilConjectures for the item id: no declaration. Concept search found
  generic exponent and finite-coefficient operations, none stating these equations.
- rg of Sheaf found vectorTensorComparison and vectorExponentIndependence in
  VectorIntegrationSiteComparison. Read their full signatures: the first has only
  the one-exponent TensorCompatibility conclusion; the second has only the global
  pro-etale vector trace equation. Neither includes the projective, open, ordered,
  coefficient, transpose and inverse exponent equations of this node. Reused the
  published underlying definitions instead of rebinding an incomplete match.

No node correction and no disputed mathematical statement. Compilation was repaired
by explicit source/target interfaces and a generic decomposition predicate, keeping
all equation clauses. Every variable and universe is explicitly bound.

## Second reading by N5

The dispatcher expressly forbids starting another agent; this is a separate in-thread
rereading, not a claim of an independent worker review. I reread the node, all helper
predicates, and the theorem signature. The first attempted direct formula exposed a
binder mistake in the ordinary tower's datum family (its IsNoetherian argument was
mistaken for the invertibility argument); the final family binds both. Explicit
source and target types avoid expensive unfolding. Generic decomposition equations
need HasZeroMorphisms for the biproduct maps, now present. The theorem includes no
separatedness of the base, no ramification divisibility, and no flatness assumption.
The single-exponent compatibility is obtained by s=r; all six exponent equations use
the same prescribed root tensor transition. The inverse composition order is
rho inverse followed by comparison of ordinary inverse, as required. The projective
trace equations are the inverse-decomposition equations followed by second projection.
The report identifies the absent proof-only module rather than silently duplicating
it. Independent mathematical review remains with the maintainer as in the brief.
