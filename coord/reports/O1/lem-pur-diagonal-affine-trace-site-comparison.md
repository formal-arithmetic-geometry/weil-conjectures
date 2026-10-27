## Worker report

The main module `Sheaf.Paper.DiagonalAffineTraceSiteComparison` states
`WeilConjectures.PurityFiniteSetting.DiagonalAffineTrace.diagonalAffineTraceSiteComparison`.
The coordinate module supplies canonical changes of source, intrinsic realization
transport, inverse projection,
and the actual ordinary and pro-etale ordered integration arrows. No theorem is proved;
every postponed proof has its natural-language proof and source in its docstring.
The item's mathematical statement is unchanged.

Hypotheses and objects, clause by clause:

- `F : FiniteFieldDatum` and `C : F.CoefficientDatum` are exactly the recorded algebraic
  closure of the finite field and prime different from its characteristic. The finite
  extension is `E : IntermediateField (Padic C.l) C.Qbar` with its
  `FiniteDimensional (Padic C.l) E` instance. `n : ℕ` indexes the coefficient level
  `n + 1`, so every positive level occurs, including level one. `projectionSetting`
  is the recorded datum, not a replacement coefficient ring.
- `S : Scheme.{u}`, `aS : S ⟶ Spec (.of F.k)`, and the explicit
  `[LocallyOfFiniteType aS] [QuasiCompact aS] [IsSeparated aS]` in the main theorem
  render separated finite type over k. Noetherianity and invertibility of ell are
  derived inside the coordinate definitions; they are not additional assumptions.
- `d : ℕ` is the arbitrary nonnegative rank. `affineTraceTower S d` and
  `affineTraceProjection S d` are the recorded ordered coordinate model of affine
  d-space, canonically identified with Mathlib affine space by
  `affineTraceAffineSpaceIso`. Thus the map is the affine projection, with ordered
  coordinates retained. `projectionSmooth` supplies its smooth relative dimension
  from polynomial charts, with the zero projection equal to the identity.
- `K : Scheme.proEtaleDerivedCategory S ...Ring` and
  `hK : finiteTorConstructible C.l E (n + 1) ... S K` use the original intrinsic
  small-pro-etale object and the recorded bounded constructible finite-Tor predicate.
  The small site keeps its object universe u+1 and morphism universe u.
- `actualMaps` literally calls `P.smoothPurityMap` on this K and
  `P.coefficientValuedSmoothTrace` on this K. The latter is the recorded compact-support
  image of gamma followed by the actual exceptional counit. No alternative purity
  or trace is substituted. Sigma types retain the computed endpoints; the `HEq`s
  compare actual morphisms after the canonical, independently specified source maps.
- `r : ℕ` indexes every positive exponent r+1. `hA` is precisely annihilation of the
  lifted finite coefficient ring by ell^(r+1). The quantified `Ke`, `hKe`, and `eK`
  are any ordinary bounded constructible finite-Tor representative of the original K,
  not a restriction that K be supplied with additional structure. Existence of such
  representatives is the constructible-origin theorem, with Tor reflected by
  `ComparisonTorAmplitude`; the main equalities hold for every representing isomorphism.
- `OrdinarySource` names the common pulled-back coefficient tensor the shifted
  ordered line, without changing that object. `Etale.affineLinearBaseCoefficient` is the ordinary mu_(ell^(r+1)) tensor coefficient,
  with its ordered d factors and shift 2d. `exponentIso` uses the normalized root-power
  transition in whichever direction the exponents are ordered. `sourceCoordinates`
  uses the recorded shift reassociation, pullback comparison at eK, that transition,
  and inverse tensor comparison. `transportedMaps` specializes these coordinates to K.
- `ordinaryTrace` is the actual ordered restricted Kummer projective-line counit,
  in the coefficient coordinates supplied by `coefficientIso` and `ordinarySourceIso`.
  `ordinaryIntegration` is `Etale.tensorTraceProjection`, including its two Koszul
  symmetries to give coefficient-first projection, inverse projection, tensor trace,
  and right unitor. `ordinaryTranspose` is the actual ordinary exceptional Hom bijection.
- `proTrace` uses `counitSource` followed by the published `orderedIntegration`, whose
  body uses independently constructed pro-etale line counits. It is not defined as
  the ordinary trace's image. `projectionIso_existsUnique` fixes the inverse
  projection by its inverse being the actual `comparedModuleProjection`; uniqueness
  determines the whole isomorphism. `proIntegration` tensors the actual pro trace
  after this inverse projection and follows with the unitor.
- `transportCoordinates` applies the actual `boundedSiteRho`, namely the image of
  the comparison unit for the ordinary exceptional functor, then eK. This is the
  recorded counit-preserving exceptional comparison. On compact support it applies
  `sfIntrinsicCompactSupportComparison`, the integration map, eK, and the intrinsic
  realization equivalence's counit. These maps fix the endpoints independently of gamma.
- `integrationInput` only re-expresses the same proIntegration arrow in the
  purity datum's coefficient alias. `integrationInput_existsUnique` fixes its
  heterogeneous equality with that original arrow; its proof is the endpoint
  identity of the two presentations of the same lifted coefficient quotient.
  This is a uniquely specified transport, not a new choice of integration.
- `MapAgreement` packages `SameMaps` on the original and transported pairs;
  `TraceSquare` packages the actual `IntegrationSiteSquare`. The normalization
  predicates are `ProjectiveNormalization` and `RankZeroActual`.
- The first component of `SameMaps` in `Conclusion` is gamma = C_V(eta^e), including those source
  and exceptional comparisons. The second component is s = a^p on the original K.
  The `IntegrationSiteSquare` clause is `beta.inv.app ... ≫ proIntegration = C_S.map ordinaryIntegration`,
  where beta is the recorded proper-counit-mate/open-extension support comparison
  evaluated at exactly pullback(Ke) tensor L_r. Combining the trace equality and site square gives the node's displayed s beta = C_S(a^e).
- The projective normalization clause is the actual `projectiveH ≫ projectiveTrace = 𝟙 unit`, namely
  t_q h_q = 1 on the prescribed Kummer class, for the infinity Cartier divisor.
  The last conjunct is `RankZeroActual`, namely `SameMaps` between
  `actualMaps ... 0` and `rankZeroMaps`. It directly equates both actual maps at rank
  zero to the independently specified identity arrows. `rankZeroOrdinarySource`
  uses identity pullback and the right tensor unit; `rankZeroOrdinarySupport` uses
  the canonical identity compact-support comparison. The purity identity uses
  `rightDerivedUpperShriekIsoOfIso` followed by `leftDerivedUpperStarId`. The trace
  identity uses compact support of that unit source, the proper/open comparison,
  ordinary identity support, and the intrinsic realization counit. These
  definitions use neither `towerCounit` nor the actual purity or trace arrows.
- Every positive annihilating exponent is universally quantified and its canonical
  comparison to the fixed diagonal exponent is retained. Thus the same original
  gamma and trace agree for all exponents. There is no assumption concerning the
  ramification index, divisibility of the coefficient level, or flatness over Z/ell^r.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `PurityFiniteSetting`, its `Ring` and `Coefficient`;
  `Sheaf.Paper.AffineDiagonalTateCoordinates`: `projectionSetting`.
- Mathlib `AlgebraicGeometry.AffineSpace` and scheme morphism properties; the actual
  affine tower and its projection, compactification and Noetherian instances come
  from the imported affine-trace construction. Mathlib's small pro-etale site is
  `Scheme.ProEt.topology`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: ordinary torsion and derived
  module categories. `Sheaf.Paper.FiniteTorAmplitudeSites`:
  `finiteTorConstructible` and `finiteTorConstructibleEtale`.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: the specified intrinsic
  coefficient twists, through the recorded finite-level diagonal twist interface.
  `Sheaf.Paper.DerivedPullbackTensorHom` and
  `Sheaf.Paper.ExchangeProjectionSuppliedDomains`: tensor/pullback and projection
  conventions, specialized by the finite coefficient interfaces used here.
- `Sheaf.Paper.SmoothPurityMap`: `smoothPurityMap`, `smoothPurityPullbackComparison`,
  `smoothPurityComparisonTensor`, `smoothPurityReassociation`,
  `smoothPurityExceptionalOver`, and `diagonalTwistEtale`.
- `Sheaf.Paper.SmoothTrace`: `smoothCompactSupport`, `coefficientValuedSmoothTrace`.
  `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`:
  `sfIntrinsicCompactSupportComparison`, intrinsic realization equivalence.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `rightDerivedLowerShriekOfCompactification`; the ordinary exceptional functor and
  `rightDerivedUpperShriekAdjunction` use the same canonical compactification.
  The finite exceptional comparison realizes
  `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`' specified system.
- `Sheaf.AlgebraicGeometry.ProjectiveLineTrace`: `projectiveLineTrace` and its datum;
  `Sheaf.AlgebraicGeometry.VectorBundleIntegration`: its ordered affine specialization.
- `Sheaf.Paper.VectorIntegrationSiteComparison`: `finiteTypeSiteComparison`,
  `projectiveH`, `projectiveTrace`, `baseExponentComparison`; its public coordinate
  modules give `comparison`, `orderedIntegration`, `towerCounit`,
  `comparedModuleProjection`, `proTensorIntegrate`, and `rightUnit`.
- `Sheaf.Paper.TensorTraceTranspose`: `Etale.tensorTraceProjection`;
  `Sheaf.Paper.AffineLinePurityComparison`: `primeUnit`.
  `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed` provides the recorded
  comparison pullback specialized by `comparison`.
- The unused imports `Sheaf.Paper.ProjectionPurityAgreement` and
  `Sheaf.Paper.ComparisonTorAmplitude` have been removed as requested (F3).
  `lem-pur-affine-ordered-integration-transposes` has no recorded Lean module at the
  time of this delivery; its exact role remains in the main theorem's proof docstring.

Edge cases checked against the definitions: d=0 (empty ordered tensor and identity
projection/adjunction), d=1 (one restricted P1 trace), K=0, empty S, coefficient level
one, annihilating exponents both below and above the diagonal exponent, and ramified
levels not divisible by the ramification index. Coefficient boundedness explicitly
requires the exponent invertible on its scheme; in the main statement this follows
from ell different from p, including the empty scheme.

Searches: msearch LeanFinder for the smooth-purity/ordered-Kummer trace site comparison
returned only general affine/smooth/etale geometry, no match; Loogle
`CategoryTheory.Adjunction.homEquiv_symm_apply, CategoryTheory.Adjunction.counit`
returned the generic inverse-transpose identity, not the geometric statement; Mathlib
Grep `smoothTrace|smoothPurity|Kummer.*trace` in AlgebraicGeometry returned no hits.
`rg` in both `lean/WeilConjectures` and `lean/Sheaf` found the existing constituent
maps, but no combined assertion. The exact node-id grep in WeilConjectures returned
no hit. The coordinate-node searches are preserved in that node's `mathlib_searches`
from the actual msearch log, including LeanSearch, LeanFinder, Loogle and Grep.

No STATEMENT-DISPUTED finding or correction of the item's statement.

## New nodes

`def-pur-diagonal-affine-trace-coordinates`, module
`Sheaf.Paper.DiagonalAffineTraceCoordinates`, packages the missing canonical source
coordinates and the specialization of the ordinary/pro-etale integration arrows
needed to state the comparison in the diagonal purity map's coordinates. It reuses
all existing geometric, Tate, tensor, support and counit constructions. Its inverse
projection is fixed by an existence-and-uniqueness characterization of the inverse
of the actual projection map; no data is chosen from mere existence. The applicability facts (smooth dimension, bounded root coefficient, invertibility
of prime powers, and invertible finite-Tor projection) are named postponed theorems with full proof docstrings and included in
the new node's statement. Blueprint search for `affine trace coordinates` returned
zero nodes. Grep found the item's statement and the existing vector-integration
identity, neither owning these source-coordinate definitions; the Mathlib searches
returned only generic isomorphism or affine-chart operations. Source is the same
Kummer-normalization sentence in the current main-20261015 dualizing-object-purity
unit. No dependency record is replaced.

Validation on 2026-10-23: both delivered modules and the existing-definition
probe compiled cleanly under the normal per-file limit. The repaired packet passed
`deliver2.py --no-push` (commit `3c143c03e7e`). A final dry run below also checks
the complete ordinary-construction ownership citation before delivery.


`def-pur-tensor-trace-projection-arrows` is an `existing: true` ownership record for
`AlgebraicGeometry.Etale.tensorTraceSymmetry` and
`AlgebraicGeometry.Etale.tensorTraceProjection` in `Sheaf.Paper.TensorTraceTranspose`.
It records the exact existing signed symmetry and coefficient-first integration
composite, including both symmetries, the inverse operator on the actual projection,
tensor trace and right unitor. No declaration is copied. The Mathlib LeanSearch query
returned only generic unitors, Loogle did not know these project names and Grep found
no Mathlib match. Project Grep located the exact definitions at lines 40 and 54;
no DAG definition node owned them. Blueprint search `tensor trace` returned only
the unrelated conjugate-tensor-traces lemma. The source is co-smoothness clause 2
and the item's Kummer-normalization sentence.

## Repair of returned head eba4dd1c4901

F1: the coordinate node no longer cites `lem-pur-tensor-trace-transpose` or
`lem-pur-vector-integration-site-comparison` for definitions. It cites the new
existing definition owner `def-pur-tensor-trace-projection-arrows` and the published
owners `def-pur-proetale-ordered-integration`, `def-pur-finite-site-tensor-projection`,
`def-pur-finite-site-coordinates`,
`def-sf-compact-support-site-comparison-construction`,
`def-pur-bounded-site-transpose-arrows`, `def-pur-supported-projective-chern`,
`def-pur-supported-projective-site-arrows`, `def-pur-proetale-affine-line-counit`,
`def-amb-affine-trace-tower`, `def-amb-affine-trace-construction`,
`def-amb-affine-linear-trace-action`, and
`def-amb-vector-integration-charts`. The declaration ownership was checked against
their current Lean records and sources. In particular these own `orderedIntegration`,
`comparedModuleProjection`/`proTensorIntegrate`, `comparison`/`baseExponentComparison`,
`compactSupportSiteComparison`, `boundedSiteRho`, `projectiveH`, `projectiveTrace`,
`infinityCartier`, the actual tower/projection/compactification,
`affineLinearBaseCoefficient`/`affineLinearCoefficientDescent`/
`affineLinearCompactComparison`, and `vectorIntegrationBaseCoefficientPullback`.

F2: the tautological `RankZeroCounit` was deleted from the coordinate module,
its definition node statement and declaration list. The item's actual conclusion
now includes `RankZeroActual` on the original intrinsic K. The independently
constructed `rankZeroMaps` gives the canonical identity/unit reference pair and
`SameMaps` compares each actual arrow against it. All ordinary representatives,
representing isomorphisms and annihilating exponents remain quantified; this adds
no hypotheses. The actual zero-rank assertion is available for the smooth-purity
corollary, rather than being inferred solely from the ordered counit's specification.

F3: both unused proof imports were removed from the item module.

## Self-check of repaired statements

Read the item and its current blueprint normalization sentence against the repaired
conclusion. The arbitrary finite extension, every positive coefficient level,
separated finite-type base, original intrinsic finite-Tor constructible K and every
rank d are retained. `MapAgreement` still pins the two actual maps, `TraceSquare`
still evaluates beta on the specified tensor source, and projective normalization
is still t h = identity. The zero-rank clause now compares the actual purity and
trace to canonical identities, independently of the tower counit specification.
Checked d=0, d=1, zero K, empty base, coefficient level one and annihilators on either
side of the diagonal exponent. The item statement itself is unchanged. The new
existing-definition node uses precisely the existing arrows, and the coordinate
node's revised dependency list names their definition owners.

Final ownership self-check also adds `def-amb-affine-trace-construction`, which
owns the ordinary `Etale.affineTraceLeft`, `Etale.affineTraceRight` and
`Etale.affineTraceCounit` used in `ordinarySourceIso` and `ordinaryTrace`. The
item declaration list now includes `rankZeroUnitSource` and
`rankZeroOrdinarySource_existsUnique`, as well as its canonical source transport.

## Second reading by O1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
