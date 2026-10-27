## Worker report

This delivery states the node in Sheaf.Paper.AffineCoefficientCounitNormalization,
using the canonical map definitions in Sheaf.Paper.AffineCoefficientCounitMaps.
All four theorem declarations have sorry proofs; every definition has actual data.
The declaration list records all helpers and all clauses of this single node.
This is the repair of returned immutable head 7afdcfb1dac4; its mathematical
statements are retained and its three extraneous theorem dependencies removed.
There is no statement correction and no dependency repair.

### Hypotheses and coefficient coordinates

- The fixed field, distinct primes, finite extension, positive level and valuation
  quotient are P : WeilConjectures.PurityFiniteSetting. Ring P is the recorded
  AffineLinePurity.Ring, with the recorded ringEquiv P to P.Coefficient. Its
  finiteTateCoefficient index P.level - 1 denotes the positive quotient level
  (P.level - 1) + 1 = P.level. No ramification-divisibility assumption is made.
- Y and aY : Y → Spec P.field.k, with LocallyOfFiniteType, QuasiCompact and
  IsSeparated aY, express precisely separated finite type over the fixed field.
  Noetherian instances in the conclusions are derived from finite type, not assumed.
- K is in the actual ModuleCat small-pro-etale derived category. The hK binder is
  DerivedCategory.constructibleFiniteTor. The line theorem retains K in Plus and
  a constructible finite-Tor ordinary representative H with its actual eH to K.obj;
  every such original K has such a presentation by the first theorem.
- r : Nat with hA : ell^(r+1) = 0 indexes every positive annihilating exponent,
  including exponent one. modulusUnit is the invertible-power consequence of
  the recorded primeUnit; it is a named postponed proof, not a hollow definition.

### Clause-by-clause rendering

1. X_d and p_d are the recorded affineTraceTower and affineTraceProjection.
   Their zero stages are literally Y and identity. affineTraceToAffineSpace is
   the existing canonical identification with dimension-d affine space; no second
   affine-space definition is introduced.
2. coefficient is the actual affineTraceRight image of ordinaryFiniteUnit.
   affineLinearCoefficientDescent identifies this with p_d^* A(d)[2d]; this is
   the existing ordered shifted-Tate construction. trace is the actual composed
   affineTraceCounit, transported by affineLinearCompactComparison. These are
   the standard-frame coordinates of the recorded vector integration.
3. FiniteAffineNormalization's first existential supplies a bounded constructible
   finite-Tor ordinary H and Nonempty (comparison.obj H ≅ K). Its quantified a,b
   equivalence says the SAME interval on the two sites, not merely existence of
   some interval. No a ≤ b restriction silently discards the zero-object cases.
4. Domains quantifies d,c and signed shift s. The inline derived pullback/tensor-with-finiteEtaleTateTwist/shift
   construction stays bounded constructible and has interval [a-s,b-s] whenever
   H has [a,b]. The natural Tate powers c cover every finite product of the
   line factors used in the ordered coordinate calculation, including c=0.
5. Domains separately asserts bounded constructibility of coefficient at every d,
   every affineLinearBaseCoefficient product b on every coordinate scheme, and
   the actual affineTraceLineLeft image of affineTraceLineRight applied to those
   products. These give the bounded ordinary origins of the stated source factors.
6. OrdinaryProjectionDomain is IsIso of the actual Etale.projectionMap component.
   ComparedProjectionDomain is the existing ProjectionInvertible predicate at the
   actual HasCompactification.compactification, with the compared objects.
   Domains applies both to every coordinate pair (d,b,c,s), to (L,H), and through
   DualizingProjectionDomain to (omega,H). No arbitrary projection is supplied.
7. Domains asserts IsNoetherian and an explicit finite natural Krull-dimension
   bound for every coordinate scheme, and for each compactification whose
   structure morphism is IsProjective. Compactification already retains properness.
   These are exactly the geometry domains for the bounded exceptional Hom maps.
8. UnitTransposeInvertible says the actual exceptional transpose of trace at A is
   invertible. TensorEquation explicitly uses the signed symmetry followed by
   Etale.dualizingComplexTensorMap, and on the right the actual adjunction homEquiv
   of signed symmetry, inverse Etale.projectionMap, signed symmetry, tensor with
   the trace, and the right unitor. These are exactly the composites previously
   named tensorTraceTheta and tensorTraceIntegrated, with no use of that theorem.
   Its left
   factor is tensor of the actual adjunction homEquiv of trace, so its equation
   is theta (1 tensor P) = P_H, with canonical Koszul symmetries and unitors.
   TensorNormalization quantifies every d, including d=0. As in the recorded
   cohomological-smoothness interface, this is equality in canonical ordinary
   comparison coordinates; the site comparison identifies these exact maps.
9. lineSourceIso is built from ordinaryFiniteTensorPullback, the geometric
   leftDerivedUpperStarComp and the canonical coefficient equality. lineCounit
   is its inverse followed by the counit of affineTraceLineAdjunction, which is
   the ACTUAL composite of the open adjunction and normalized projective datum.
   finiteLineCounit changes only to the recorded etaleSource coordinate.
10. lineTrace is pushforward of the actual open-extension counit, then the existing
    projectiveLineTrace. finiteLineTrace specializes its coefficient to the recorded
    etaleCoefficient through etaleCoefficient_eq. This is exactly I_S in the node.
11. lineProjection changes to the fixed affine-chart compactification, applies
    the signed symmetry, Etale.projectionMap, and pushforward of the signed
    symmetry, and changes back. LineNormalization asserts
    an isomorphism e whose HOM IS THIS PROJECTION and whose inverse, followed by
    1 tensor I and the right unitor, equals the actual counit (including source
    reassociation). This is equivalent to IsIso and use of its canonical inverse:
    an isomorphism with prescribed hom is unique. It introduces no new assumption.
12. LineCompatibility contains the ordinary normalization and the equality between
    realizeCounit and the existing AffineLinePurity.augmentation. realizeCounit
    uses the specified compactSupportSiteComparison, the specified sourceComparison
    and eH; the equation is the actual site comparison square, not just existence
    of some comparison. Its last equation applies specifiedExceptionalHomEquiv
    with the retained sourceWitness and identifies the resulting map EXACTLY with
    affineLinePurityComparison. This is the recorded map on the original range,
    and the same all-positive-level formula elsewhere.
13. lineSourceTransition tensors the specified comparisons to the SAME pro-etale
    Tate line, using coefficientTwistIso and its inverse. The final theorem asserts
    equality of both actual augmentations (after pushforward of that transition)
    and their actual transposes. It thus states independence of every positive
    annihilating exponent under the specified normalized transitions.

### Dependency declarations

- `def-pur-conventions`: `Sheaf.Paper.PurityFiniteSetting` — `WeilConjectures.PurityFiniteSetting`.
- `def-weil-scheme-morphism-properties`: `None` — `None`.
- `def-sbc-affine-space`: `convention / Mathlib` — `{'declaration': 'AlgebraicGeometry.AffineSpace', 'file': 'Mathlib/AlgebraicGeometry/AffineSpace.lean', 'line': 44, 'how': 'specializes in one line: take coordinate type ULift (Fin n). AffineSpace (line 44) is exactly the alternative base-change definition in Stacks 01M0/01LZ; over (line 66) is the f`.
- `def-weil-derived-pullback-tensor-hom`: `Sheaf.Paper.DerivedPullbackTensorHom` — `WeilConjectures.commonStageDerivedInternalHom_existsUnique`.
- `def-coefficient-twists-detailed`: `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted` — `WeilConjectures.sfQbarTwistingFunctor`.
- `def-compact-support-direct-image-detailed`: `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport` — `AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport`.
- `def-weil-exceptional-inverse-image`: `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` — `WeilConjectures.ConstructibleExceptionalCoefficients.System`.
- `def-amb-vector-integration`: `Sheaf.AlgebraicGeometry.VectorBundleIntegration` — `AlgebraicGeometry.Etale.vectorBundleIntegration`.
- `lem-pur-vector-integration-site-comparison`: `Sheaf.Paper.VectorIntegrationSiteComparison` — `AlgebraicGeometry.ProEtale.VectorIntegrationSite.finiteTypeSiteComparison`.
- `def-exchange-projection`: `Sheaf.Paper.ExchangeProjectionSuppliedDomains` — `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`.
- `def-weil-finite-tor-amplitude`: `Sheaf.Paper.FiniteTorAmplitudeSites` — `WeilConjectures.finiteTorConstructibleEtale`.
- `def-sf-comparison-derived-pullback`: `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed` — `AlgebraicGeometry.ProEtale.siteComparisonDerivedPullbackPlus`.
- `thm-sf-ambient-adjoint-class`: `Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom` — `AlgebraicGeometry.ProEtale.specifiedExceptionalHomEquiv`.
- `def-pur-co-smoothness`: `Sheaf.Paper.CohomologicalSmoothnessFiniteComparison` — `AlgebraicGeometry.ProEtale.IsCohomologicallySmoothFiniteCompared`.
- `def-amb-p1-trace`: `Sheaf.AlgebraicGeometry.ProjectiveLineTrace` — `AlgebraicGeometry.Etale.projectiveLineTrace`.
- `lem-amb-affine-space-top-trace`: `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace` — `AlgebraicGeometry.Etale.exists_affineSpaceTopTrace`.
- `def-pur-affine-line-purity-comparison`: `Sheaf.Paper.AffineLinePurityComparison` — `AlgebraicGeometry.ProEtale.AffineLinePurity.affineLinePurityComparison`.

The added landed statement dependencies are def-kun-derived-tensor
(Etale.derivedTensor, with its canonical signed derived braiding),
def-asd-finite-etale-tate-twist (Scheme.finiteEtaleTateTwist), and
def-pc-projective-morphism (IsProjective). The existing def-pur-co-smoothness
supplies Etale.dualizingComplexTensorMap through its recorded upstream import.
The actual inverse image is Etale.upperStar.mapDerivedCategory; the ordinary
projection remains Etale.projectionMap from the compact-support interface.
The theorem nodes lem-pur-tensor-trace-transpose,
lem-sp-etale-pullback-twist-tor-window and lem-asd-compact-projection-exchange
are absent from both delivered stmt_deps lists. None of their conclusions is
needed to state this item, and none of their helper names occurs in the source.
Proof dependencies with published statements are plain
imports, including PullbackTorAmplitude, TwistPreservesFiniteness,
ProEtaleFiniteTorComparisonNoetherian, EtaleFiniteTwistPullback,
FiniteCompactProjectionFormula and VectorBundlePurity. The recorded
lem-pur-coordinate-line-adjunction has no published Lean binding; the actual
composed adjunction needed here is already supplied by the statement dependency
lem-amb-affine-space-top-trace, through AffineTraceConstruction. No downstream
statement is assumed to define the counit.

### Edge cases

- d=0 uses the literal identity tower and its identity adjunction. The trace is
  the identity under the existing compact-support coordinate comparison; the
  quantified tensor equation is therefore the identity-adjunction formula.
- d=1 uses the actual standard affine chart of the projective line.
- Empty schemes and K=0 or H=0 are never excluded. Interval statements quantify
  all endpoints, including reversed intervals. The displayed coefficient sources
  and targets then give the unique zero-object arrows. No Nonempty scheme or
  nonzero coefficient hypothesis is present.
- Positive level one and ramified levels are included by P.level_pos and the
  existing ringEquiv. The annihilator is arbitrary, not tied to the level.
- No reducedness, geometric-fibre equality or arbitrary orientation is assumed.

### Searches

- msearch.py leanfinder: "Affine space finite coefficient etale origin Tor interval
  tensor integration transpose counit normalization" returned eight unrelated
  etale-presentation results; no exact statement.
- msearch.py loogle: '"counit", "tensor"' returned twelve generic monoidal-adjunction
  identities (including Adjunction.map_μ_comp_counit_app_tensor), not the specified
  compact-support counit, domain statements or normalized trace.
- msearch.py grep: 'affine.*counit|counit.*affine|integration.*transpose' returned
  zero Mathlib matches.
- msearch.py leansearch: "The affine line compact support adjunction counit is
  inverse projection formula followed by tensor with normalized restricted
  projective line trace" returned generic change-of-rings and sheaf counits;
  none has the actual line compactification and the required normalized maps.
- rg in WeilConjectures and Sheaf for affine/counit/integration/transpose found
  the existing TensorTraceTranspose, AffineTraceLinePurity, LineCounitBaseChange,
  AffineLinePuritySource and AffineLinePurityCoordinateMaps. Their full signatures
  were inspected and their existing constructions reused. None jointly states
  this node's domains, tensor normalization, exact ordinary counit comparison
  and exponent independence. grep for this exact node id found no upstream owner.

### Validation

Only the prescribed scompile.py server compilation is used. Diagnostic probes
under probe/ are not delivered. The saved packet's required initial deliver2
--no-push passed (10009fc2c24), confirming the repair is ownership-specific rather
than a compiler repair. The two modified modules passed the prescribed separate server compile in
dependency order: Maps sandbox 29.2 s and library 38.7 s; Normalization sandbox
52.0 s and library 39.5 s. No errors or unexpected warnings were reported.
The metadata self-check confirms exact recorded signatures, complete declaration
lists, unchanged item statement, and the 100-character line limit.

## New nodes

def-pur-affine-coefficient-counit-coordinate-maps owns
Sheaf.Paper.AffineCoefficientCounitMaps. It constructs the actual coefficient,
trace, tensor source comparison, composite line counit, restricted projective
trace, fixed compactification projection, comparison realization and normalized
exponent source transition. These composites were absent: the underlying
adjunctions, traces, source objects and site comparisons are all reused.
Its signed coefficient-first projection is written inline as symmetry,
Etale.projectionMap, and compact pushforward of symmetry, using the existing
Etale.derivedBraidedCategory. It cites def-kun-derived-tensor and
def-exchange-projection instead of lem-asd-compact-projection-exchange.
There is no new definition of the already existing compactProjectionMapCoeffFirst:
lineProjection is the owning node's fixed-compactification transport of that
composite, which was already present in the original delivery.
The only postponed proof in this definition module is modulusUnit, the explicit
invertibility consequence required by the constructions. It is included in the
new node's statement and has its complete proof plan in its docstring.

The new-node searches were: blueprint_refs.py search "affine coefficient counit
coordinate" (zero nodes); rg for lineSourceTransition, finiteLineCounit,
realizeCounit and lineSourceIso in dag/nodes, WeilConjectures and Sheaf (no matching
definitions); msearch grep of those names (zero Mathlib matches); LeanFinder
"Canonical coordinate maps for the affine line counit with shifted Tate
coefficients and the restricted projective line trace" (eight affine coordinate
function results, none these counit/trace composites); LeanSearch "Define the
actual affine line counit by composing open extension and the normalized
projective line adjunction using canonical tensor coordinates" (eight generic
change-of-rings, coalgebra and affine-map results, none these constructions).
Exact returned names are in the new node's mathlib_searches.

## Dependency modules

None.

## Return repaired

H2/section 1, all three instances:

1. TensorEquation no longer refers to tensorTraceTheta, tensorTraceIntegrated or
   tensorTraceProjection. Their bodies are expanded using the original canonical
   signed braiding and actual adjunction/projection/trace operations. The public
   TensorTraceTranspose import and its stmt_dep are removed.
2. The four pullbackTwistDerived occurrences are expanded to its exact definition:
   upperStar.mapDerivedCategory, derivedTensor with degree-zero finiteEtaleTateTwist,
   and the signed shift. EtalePullbackTwistTorWindow is no longer imported or cited.
3. lineProjection expands compactProjectionMapCoeffFirst to symmetry, projectionMap,
   and pushforward of symmetry, between the same compactification comparisons.
   CompactProjectionExchange is no longer imported or cited. The new coordinate
   definition node cites the existing derived-tensor definition instead.

These replacements preserve the maps and objects by unfolding the original
helper definitions; they add no map, object, hypothesis or theorem conclusion.
The current read-only main still has no Lean binding on the item and retains
its original statement and dependency list. The delivery wrapper rebases this
repaired packet onto current main without direct Git commands in the read clone.

## Second reading by Q11

Self-check by the assigned worker (the dispatcher explicitly forbids subagents):
compared both node files and both modules clause by clause after the repair.
The finite coefficient setting, separated finite type, exact same Tor interval,
all coordinate dimensions and shifts, the omega projection domain, finite
Krull bounds, tensor equation, actual line counit/site comparison/transpose, and
independence of every positive annihilator exponent are retained. Only concrete
composite expressions and their definition dependencies changed. In particular
beta is the same Etale.derivedBraidedCategory used by tensorTraceSymmetry, the
pullback uses mapDerivedCategory as in pullbackTwistDerived, and lineProjection
has the same coefficient-first ordering and signs as the removed helper call.
The edge cases d=0, zero and empty objects, n=1 and ramified n remain included.
OrdinaryProjectionDomain remains a conclusion, not an added hypothesis; its
available global instance is consistent with the node's explicit domain clause.
modulusUnit remains the named postponed proof already covered by the coordinate
node's invertibility statement and proof docstring. No extra proof is inserted.

The expanded inverse projection explicitly registers the published
Etale.isIso_projectionMap_of_finite instance in TensorEquation. This is the same
canonical invertibility used internally by dualizingComplexTensorMap, with no
new hypothesis or postponed theorem.

Repair search: msearch loogle `"projectionMap"` returned zero hits; msearch
LeanFinder "Affine line compact support counit equals inverse projection followed
by tensor with normalized trace" returned TensorProduct.counit_def,
Coalgebra.sum_counit_tmul_map_eq, Coalgebra.sum_counit_tmul_eq,
Coalgebra.sum_tmul_counit_eq, Pi.counit_comp_finsuppLcoeFun,
Coalgebra.sum_map_tmul_counit_eq, coevaluation_apply_one and
DFinsupp.counit_comp_lsingle. None is the specified affine-line map.

For elaboration, the inverse projection is the (L,H) component of the inverse
natural transformation, rather than inv of its component. These are the same
canonical inverse by the inverse identities. The full transformation's published
invertibility is registered explicitly; no component-invertibility hypothesis
is introduced.
