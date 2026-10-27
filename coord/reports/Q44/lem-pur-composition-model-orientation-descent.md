## Worker report

The module `Sheaf.Paper.CompositionModelOrientationDescent` states the complete model
and descent package as `WeilConjectures.PurityFiniteSetting.composition_model_orientation_descent`.
Its only theorem has proof `sorry`. The auxiliary definitions contain actual
canonical composites or propositions spelling out the conclusions; none supplies an
arbitrary orientation, comparison map, or premise of the desired equation.
No dependency record or mathematical statement was changed, and no new DAG node is needed.

Hypothesis and clause correspondence:

- The whole finite datum, including p prime, positive a and n, fixed algebraic closure,
  ell different from p, finite E/Q_ell, valuation ring and uniformizer quotient, is the
  recorded `P : PurityFiniteSetting`. `P.Coefficient` is its standard ULift coefficient
  ring for fixed-ring sheaves, canonically equivalent to the intrinsic constant-ring
  encoding. This imposes no divisibility of n by the ramification index.
- Schemes and maps are `{X Y Z : Scheme.{u}}`, `f`, `g`, and `aZ`. The other structure
  maps are the composites `g ≫ aZ` and `f ≫ g ≫ aZ`. This is the explicit-structure-map
  version used by the recorded DNC and diagonal interfaces. Finite type is
  `[LocallyOfFiniteType] [QuasiCompact]` on the relevant maps. Pure dimensions are
  `[SmoothOfRelativeDimension d f]` and `[SmoothOfRelativeDimension e g]`, with `d e : ℕ`.
  Separatedness is assumed only on f and g. Absolute separatedness is never added.
  Noetherianity, compactifiability, compact targets and composite smooth dimension are
  installed internally from recorded consequences, not imposed as extra hypotheses.
- The derived category is the actual pro-etale fixed-ring module-sheaf category;
  tensor is `ProEtale.derivedTensor` through `compatibleTensorIso`, and inverse image
  in the orientation equation is the actual left-derived `ProEtale.upperStar`.
- The recorded tensor-mate omega uses the derived tensor unit, whereas the specified
  diagonal orientation uses the comparison image of the degree-zero constant unit.
  `modelOrientationUnit` applies the actual exceptional functor to the canonical
  `DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso` and
  `smoothPurityUnitIso`. `modelOrientation` then composes with exactly
  `diagonalDualizingObject`. This is a scalar-coordinate comparison, not a new omega.
- Mu is `modelOrientationMu`: canonical roots/Tate pullback followed by the tensor
  of identity with that pullback and `modelOrientationPowerMul`. The latter is the
  inverse of the recorded ordered power splitting, transported by the recorded
  comparison tensor constraint. The powers `diagonalTwistEtale` already include
  the shift 2r. Thus no generator or independently chosen trivialization enters.
- `ModelOrientationSourceNaturality` says that the recorded `compositionSourceFixed`
  satisfies its complete eight-factor `CompositionSourceNormalized` and that
  `compositionSourceIdentification` commutes with every morphism of finite-Tor
  constructible inputs. The endpoints are the recorded shifted pullback functors.
  The next conjunct states the even-block sign `(-1 : ℤ)^((2*d)*(2*e)) = 1`.
- Affine B is quantified with `[IsAffine B]` and a finite-type structure map aB.
  `modelOrderedGamma` destructs the positive-level datum and uses `chartGamma` at its
  successor level. `chartGamma` is the actual composition of `chartProjectionUnitSource`
  inverse with `projectionAffineInPresentation`; the latter calls the recorded
  `affineSpacePurityComparison`. Thus every n>=1, including ramified n=1, uses Gamma.
  The conclusion asserts an isomorphism family G with its hom fixed by
  `ModelGammaNormalization`: pull back that recorded Gamma through the specified
  `modelOrderedCoordinates`, then the canonical `modelCoordinateDualizing`. The
  coordinate iso is required to have exactly that hom, not an arbitrary frame.
  Its outermost-line coordinate is the last finite affine coordinate, so the
  order agrees with successive coordinate adjunction, including the empty list.
  This existential is part of the theorem, not data chosen from bare existence.
- `ModelAffineOrientationEquation` states the first affine identity. The total
  factor `modelAffineTotalOrientation` is G_(d+e) inverse after the actual unit
  comparison and q P_e=P_(d+e) transport. The q factor `modelAffineQOrientation`
  is the inverse smooth exceptional base-change mate for the Cartesian square
  `DiagonalPasting.affineGeometry`, followed by pullback of G_d inverse and Tate
  restriction. The second factor is the pullback of G_e inverse. The sigma is
  `CompositionTensorMate.sigma`, and Mu is the recorded ordered concatenation.
  No diagonal orientation defines any of these affine factors.
- `modelOrientationZero G B r aB` is literally Lz_r* of G_r inverse followed by
  `modelOrientationTwistPullback`. Its initial factors identify the recorded
  `compatibleStandard` source with Lz_r*omega using the coefficient-unit and
  exact comparison-site pullback maps. `ModelZeroOrientationEquation` states
  nu followed by b_(d+e) equals tensor(b_d,b_e) followed by power concatenation.
- `ModelGammaZeroNormalization` states Gamma_0=1 after the actual exceptional-id
  and pullback-id constraints on the ordered model. `ModelGammaNormalization`
  transports this convention to zero-dimensional finite-coordinate affine space.
  Both affine equations quantify d,e in Nat with no positivity requirement.
- `ModelChartOrientationEquation` states kappa followed by delta_gf and beta_gf
  equals the tensor of delta_f beta_f and f*(delta_g beta_g), followed by Mu.
  `ModelChartBetaIdentification` additionally states all three missing frame
  identifications: beta_f equals `chartNormalCoordinateComparison` followed by b_d;
  f*beta_g followed by Tate restriction equals f*normal-coordinate comparison,
  then `compatibleStandardPullback`, then b_e on U; beta_gf equals its specified
  composite-chart normal-coordinate comparison followed by b_(d+e). All x,y are
  actual etale coordinate charts over f,g, and the composite uses the recorded
  `compatibleCompositeChart` and `composition_compatible_tangent_normal` witnesses.
  The chart equation remains over all affine triples as in the accepted return.
- `ModelOrientationDetection` removes shift 2(d+e) from the specified global target,
  asserts concentration in degree zero, and asserts rank-one local freeness of H^0
  under the recorded `finiteCoefficientRealization`. Its discrete coefficient
  topology is installed internally. It then states injectivity of the actual
  derived open-restriction maps on automorphisms for every set-indexed Zariski cover,
  in particular the compatible-chart cover. The index universe w is independent;
  empty covers are included.
- The final `ModelOrientationEquation` is the global (**), using the actual
  `CompositionTensorMate.sigma` (symmetry, theta, inverse specified c) and the
  specified diagonal orientations. Its second conjunct explicitly says that the
  quotient `B.inv ≫ A` is the identity of `diagonalTwist X (d+e)`, with A=theta_gf sigma
  and B=Mu(theta_f tensor f*theta_g). The order matches Lean's left-to-right composition.
  There is no nonemptiness or connectedness hypothesis, so this includes empty X.

Dependency interfaces read and used (module, declaration):

- `Sheaf.Paper.PurityFiniteSetting`, `WeilConjectures.PurityFiniteSetting` and its quotient.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `Smooth`, `SmoothOfRelativeDimension`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `IsProper`, with `IsSeparated`.
- `Sheaf.Paper.DerivedPullbackTensorHom`, finite derived operations and
  `commonStageDerivedInternalHom_existsUnique`; the present statement uses its
  finite fixed-ring realization, not its irrelevant common-stage Hom interface.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`,
  `ConstructibleExceptionalCoefficients.System`; actual finite functor via the
  publicly available `sfFiniteExceptionalAt` / standing `rightDerivedUpperShriek`.
- `Sheaf.Paper.PurityDiagonalDualizingObject`, `diagonalDualizingObject`,
  `existsUnique_diagonalDualizingObject`, `diagonalDualizingComparison`.
- `Sheaf.Paper.CompositionTensorMate`, `composition_tensor_mate`, `sigma`, `omega`, `c`.
- `Sheaf.Paper.PurityCompositionCompatibleDncCharts`,
  `composition_compatible_dnc_charts`, `compatibleNu`, `compatibleKappa`,
  `compatibleTensorIso`, `compatibleComparisonTensor`, `compatibleStandard`.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`, `sfQbarTwistingFunctor` and
  the public finite positive interface `diagonalTwist`, `diagonalTwistEtale`.
- `Sheaf.Paper.CartesianCoefficientTwists`, `spTwists_cartesian`; finite restriction
  is the recorded `vectorIntegrationBaseCoefficientPullback`.
- `Sheaf.Paper.FiniteTorAmplitudeSites`, `finiteTorConstructibleEtale` and the public
  intrinsic finite predicate `finiteTorConstructible`, used for source naturality.
- `Sheaf.Paper.IntegralFinitePullbackComposition`,
  `integralTowerGeneralPullbackComposition`; the recorded comparison owner below
  provides its fixed-scalar exact pullback specialization.
- `Sheaf.Paper.PurityCompositionCoherence`, `compositionSourceIdentification`,
  `compositionSourceFixed`, `CompositionSourceNormalized`, `compositionEtalePowerAdd`.
  This module also states the downstream composition theorem, which is NOT used as
  a premise or proof input. Only the recorded definition-node helpers are used.
- `Mathlib.AlgebraicGeometry.AffineSpace`, `AffineSpace`, `AffineSpace.zeroSection`;
  `Sheaf.AlgebraicGeometry.VectorBundleZeroSection`, `VectorBundleZeroSection.scheme`,
  `VectorBundleZeroSection.zero`; the standard affine model uses the former directly.
- `Sheaf.Paper.AffineSpacePurityComparison`, `affineSpacePurityComparison`;
  `Sheaf.Paper.ProjectionPurityAgreement`, `projection_purity_agreement` and the
  all-positive-level `projectionAffineInPresentation` interface.

The plain proof imports are exactly the recorded additional proof dependencies:
`PurTwistSheafLocallyFree.pur_twist_sheaf_locally_free`,
`DerivedPullbackTensorIso.derivedPullbackTensorIso`,
`AffineOrderedIntegrationTransposes.ordered_integration_transposes`,
`AffineCoefficientCounitNormalization.affine_coefficient_counit_normalization`,
`VectorBundlePurity.vectorBundlePurity`,
`VectorIntegrationSiteComparison.finiteTypeSiteComparison`,
`CompactSupportSiteCoherence.compactSupportSiteCoherence`,
`DegreeZeroDerivedMapGluing.degreeZeroDerivedMapGluing` and Mathlib's
`CategoryTheory.mateEquiv_vcomp` / its horizontal and conjugate variants.
The theorem docstring gives all nine DAG proof steps and their map-level calculation.
The affine coordinate transports additionally use the public helpers from the recorded
compatible-chart module: `chartGamma`, `chartOrdinaryBaseChange`, `chartDualizingUnit`,
`chartNormalCoordinateComparison`, and the canonical exceptional `diagonalEtaleLocality`.
`modelOrderedCoordinates` uses the upstream `Scheme.Hom.toIteratedAffineLine` constructor.

Edge cases checked: d=0, e=0, both zero, K=0, n=1 with ramified E, empty affine B,
empty X with an empty open cover, disconnected X, nonseparated structure schemes,
and arbitrary universe w for the open-cover index. Every definition contains actual
data; the only sorry is the one main theorem. No STATEMENT-DISPUTED fault found.

Searches: msearch LeanFinder query “canonical smooth purity dualizing orientations
multiplicative affine zero sections descent Tate twists” returned eight unrelated
hits (AffineSpace.functor, smoothLocus and linear-algebra orientations among them).
msearch Loogle query “CategoryTheory.MonoidalCategory, CategoryTheory.Iso” returned
12 general tensor/unit/associator results, none the theorem. msearch grep query
“composition.*orientation|orientation.*descent|Tate.*twist” in AlgebraicGeometry
returned zero hits. rg in both lean/WeilConjectures and lean/Sheaf for this item id
and composition-orientation/descent terms found no statement match; nearby chart and
comparison helpers were reused. Proposed declaration names were also searched in
both project roots, Mathlib and dag/lean_names_upstream.json: no duplicates.
The wrappers recorded the three external searches in searches.jsonl.

Validation: scompile.py compiled every version separately in module mode against the
live published build; final file passed both sandbox and library checks. A stale local
namespace for the comparison-unit iso was diagnosed with scompile.py --source and
repaired to the live `ProEtale.DerivedCategory` namespace. No library files were edited.

## Repair of returned head 11935e5ddc69

F1 repaired: both affine equations now use G fixed by the recorded ordered Gamma,
not `ModelOrientationEquation` at q. The q factor is explicitly the base change
of G_d inverse; b_r is explicitly the pullback of G_r inverse and Tate restriction.
The finite affine model is linked by a prescribed coordinate map and canonical
exceptional-locality composite. Gamma_0 has its explicit identity normalization.

F2 repaired: deleted `ModelIntegrationNormalization` and all its copied
`chartOrientation_coordinate_formula_forward`, `chartStandardSection_formula`,
and `chartAffineGamma_zero` conjuncts. No equation is left stranded on the
unrelated affineTraceTower model. The existing ordered comparison is used through
its recorded all-positive-level `projectionAffineInPresentation` presentation.

F3 repaired: added `ModelChartBetaIdentification`, with the f, pulled-back g and
gf beta=b equations through the actual `chartNormalCoordinateComparison` and
`compatibleStandardPullback`. These are conclusions of the same sole theorem.

The saved-packet dry run first passed at ffb243a3d94, but the substantive self-check
confirmed these three return faults in its unchanged source. They were repaired
before a new delivery. No node statement, stmt_deps or dependency record changed.
The only changed node field is lean, whose declarations list now includes all 24
public definitions and the theorem. There are no new nodes or dependency modules.

## Second reading by Q44

I reopened the node statement, the repaired module, the current dependency sources,
and the return against immutable head 11935e5ddc69. The earlier report incorrectly
claimed that indirect chart normalization already rendered the Gamma and beta=b
clauses; the repair above replaces those claims with explicit statements.
The ordered Gamma wrapper is data from the recorded declaration, not a sorry;
its positive-level case distinction adds no ramification-index divisibility.
The coordinate iso has prescribed hom, and the normalized G has prescribed hom
under invertible canonical transports, so neither is an arbitrary orientation.
The q arrow uses inverse smooth exceptional base change before G_d inverse.
The standard-section source and Lz*omega match through actual unit/site maps.
For beta_g the pullback, standard-section base change and Tate restriction are
all explicit; the gf coordinate uses the recorded composite chart's etaleness.
The original hypotheses, source naturality, even sign, chart beta-delta-kappa
identity, rank-one concentration, arbitrary-cover Aut injectivity, global (**)
and identity quotient were retained. Checked d=0, e=0, both zero, empty affine B,
empty X and empty cover, disconnected schemes, zero K, ramified n=1, and independent
cover-index universe w. No nonempty/connected or absolute-separatedness premise
was added. Exactly one sorry remains, the main theorem; every definition has data.
No STATEMENT-DISPUTED issue or source correction is needed.

Validation: the repaired module passes scompile.py in sandbox and library module
mode, with no errors or non-sorry warnings. New declaration names were searched
with rg in Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json, with
no conflicts. Existing semantic search results above are retained. The final
preflight and delivery are run using deliver2.py only.
