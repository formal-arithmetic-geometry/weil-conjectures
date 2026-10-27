## Worker report

The delivery states `det-sp-purity-bc-factors` in
`Sheaf.Paper.SmoothPurityBaseChangeFactors`, namespace
`AlgebraicGeometry.ProEtale.SmoothPurityBaseChange`. `finite_factors` gives the
finite-ring case and `tower_factors` gives the tower case. Each states orientation,
tensor-map, and full purity-map compatibility. Both theorem proofs are `sorry`;
their docstrings carry the five-step accepted proof plan. The node statement, proof, and proof dependencies are unchanged. Its statement
dependencies gain only the new existing:true definition node described below.

The remaining nine declarations are real constructions used to type these
particular equations. They have no postponed data or extra axioms. There are no
additional Lean modules or dependency repairs. One new existing:true definition node
records the existing finite source-comparison constructors.

### Hypotheses and objects

* The global finite-field tuple is the recorded `FiniteFieldDatum.{u}`, with
  prime `ell`, `[Fact ell.Prime]`, and `_hne : ell ≠ D.p` in each theorem.
* `X`, `Y`, and `Y'` are objects of `Over (Spec (.of D.k))`; each has
  `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` on its structure map.
  The morphisms `f` and `v` are morphisms in this over category, so both are
  k-morphisms. There is no smoothness, flatness, or properness assumption on v.
* Pure nonnegative relative dimension is `d : ℕ` and
  `[SmoothOfRelativeDimension d f.left]`. Separatedness of f is explicit.
  `IsNoetherian`, `QuasiCompact f.left`, and `HasCompactification f.left` are
  typeclass certificates of consequences of separated finite type over a field,
  rather than additional restrictions on the mathematical domain. Primed
  certificates are consequences of base change and the pulled compactification.
* In `finite_factors`, X' is literally `pullback f.left v.left`, u is
  `pullback.fst`, and f' is `pullback.snd`. In `tower_factors`, the equivalent
  presentation is a specified `IsPullback u'.left f'.left f.left v.left`, with
  X' an over object. The compactification for f' is exactly `c.ofIsPullback sq`.
* Finite coefficients are arbitrary `A : Type (u+1)` with `[CommRing A]`,
  `[Finite A]`, and `hA : ((ell^n : ℕ) : A) = 0`, where `1 ≤ n`.
  No nontriviality, field, or reducedness assumption is placed on A.
  The chosen coefficient universe is the existing fixed-module presentation
  for `Scheme.{u}`, not a restriction to one particular quotient ring.
* The finite Tate source is the dependency's ordered shifted root line
  `Etale.FiniteSmoothPurity.line A (ell^n) hA X.left d`.
  `alpha` and `alpha'` have the dependency's `OrientationNormalized` property,
  using its actual `FiniteRingSectionDeformation.Geometry`. This property
  fixes the diagonal/Rees/inverse-integration orientation; alpha is not an
  arbitrary isomorphism. The witnesses `hX` and `hX'` record the invertibility
  of the same prime power on the schemes, implied by ell ≠ p.
* The finite category is presented in precisely the etale-origin coordinates
  already used by `finiteComparedTensorClause`. Every equation is mapped by
  `Etale.FiniteSmoothPurity.comparison A X'` into the actual ordinary pro-etale
  derived category. K ranges over every etale representative whose comparison
  image satisfies the intrinsic predicate `Etale.FiniteSmoothPurity.IsCtf`.
  Finite constructible pro-etale comparison supplies such a representative for
  every object in the node's domain. The canonical site/pullback/tensor
  comparisons identify the displayed maps with the node's maps; no arbitrary
  isomorphism substitutes for any of them. This presentation is the same one
  used by the recorded `def-pur-co-smoothness` and general-ring statement.
* Tower coefficients are arbitrary `E : Type u` with `[Field E]`,
  `[Algebra (Padic ell) E]`, and `[FiniteDimensional (Padic ell) E]`.
  `b`, `o`, and `q` are the published section-normalized operation and realization
  data. All tower indices n mean positive level n+1, with coefficient
  `SpTowerShriek.R ell E n = O_E/(ell^(n+1))`.
* `a : SpTowerMate.Data ... sq c` supplies the two restricted adjunctions, exact
  pullback-domain certificates, and their unit/counit-normalized finite levels.
  `x` is the specified open exchange, and `hb` certifies invertibility of the
  compact-support exchange. These are exactly the existing constructions
  supplied by `det-sp-tower-exceptional-bc`, not replacement hypotheses about e.
* `P` and `P'` are the `det-sp-tower-gamma` purity data. `TowerPurityAt` only
  presents its existing `Purity c.i c.g` at a named compactification. Its
  `QuasiCompact` certificate transports the existing one along `c.comm`, and
  the factorization itself supplies its compactification. All finite
  normalization equations of the original data are retained.
* `gu` and `gv` are the published `GeometricCoordinates` for the two horizontal
  pullbacks. Their ordinary section and adjunction-mate normalizations fix the
  site comparisons used to read the finite equations. They do not supply new
  operation functors or uncharacterized maps.
* Tower K ranges over `SpTowerCalculus.C ... Y.left`, the full uniformly bounded
  constructible finite-Tor subcategory of the ordinary derived category of
  strict varying-coefficient towers. No `IsSpNormalizedTower` hypothesis occurs.
  Tensor is always `SpTowerShriek.tensor`, the ordinary K-flat tensor.

### Clauses and specified arrows

* Finite clause (1) is the first conjunct of `finite_factors`:
  `comparison.map (u*.map alpha.inv ≫ dualizingComplexBaseChangeMap ...) =
  comparison.map (vectorIntegrationBaseCoefficientPullback.hom ≫ alpha'.inv)`.
  The latter canonical map is the generator-normalized
  `vectorIntegrationBaseCoefficientPullback` using the existing
  `PurityFiniteSetting.purityTwistTransport`. Its roots and pure-tensor equations
  characterize the same canonical transport as in the returned draft.
  In composition order this is precisely e_1 composed with u*a_f = a_f'
  after the specified Tate-source identification.
* Finite clause (2) is the first conjunct under `∀ K, IsCtf ... →`.
  `smoothTensorDualityMap` is the actual inverse-projection/counit transpose;
  `rightDerivedUpperShriekBaseChangeMap` is the transpose of beta inverse followed
  by the pulled counit. The right side first applies
  `leftDerivedUpperStarTensorIso`, then the tensor functor on
  `derivedSquareUpperStarIsoInvApp` in its first variable, then tensors with the same
  `dualizingComplexBaseChangeMap`, then applies the primed tensor transpose.
  Thus it is exactly e_K u*t_f = t_f' (1 tensor e_1), with its canonical sources.
* The finite consequence is the final conjunct, using the existing
  `Etale.FiniteSmoothPurity.gamma` on both sides and the specified
  `ordinaryFiniteTwistedPullbackComparison`, with the inverse canonical
  derived square isomorphism and the normalized Tate comparison as its two
  specified inputs. The gamma definition is tensor
  with alpha inverse followed by that same tensor transpose. The ordered shifted
  line is the dependency's tensor presentation of twist reassociation.
* `towerExchange` is the realized `SpTowerMate.mate`: inverse realization counit
  followed by realization of its underlying strict-tower morphism. The dependency
  defines that mate from inverse beta and the two actual adjunctions.
* `towerUnitIdentification` transports the coefficient-unit identification back
  through the actual inverse realization. `towerUnitExchange` is e at the unit
  followed by the primed exceptional functor applied to precisely that identification.
* `towerPullSquare` is the inverse of the published geometric square compositor,
  followed by cancellation of the intermediate realization equivalence.
  `towerTensorComparison` is the published tensor/pullback comparison followed
  by this square compositor in its first factor.
* The existential s and t in `tower_factors` are respectively pullback of the
  unit and pullback of the ordered Tate line. The first two conjuncts fix them
  by `SpTowerP1.WordComparison`, using the actual `unitWord`, `coefficientWord`,
  `pullWord`, and normalized ordinary finite pullback maps. These are equations
  for all positive levels; s and t are not unconstrained endpoint isomorphisms.
  The unit and shifted Tate lines lie in a single shifted heart, where exact
  evaluation plus single-complex full faithfulness fixes their maps. No claim
  that arbitrary derived tower maps are detected by evaluation is used.
* Tower clause (1) is the next conjunct:
  `pull.map P.orientation.hom ≫ towerUnitExchange ... s =
  t.hom ≫ P'.orientation.hom`.
* Tower clause (2) is the first conjunct for each K. The left side is pulled
  `towerTensorMap P K` followed by `towerExchange ... K`. The right side is
  `towerTensorComparison`, then the tensor functor applied to `(identity,e_1)`,
  then the primed `towerTensorMap` at the actual restricted pullback V(K).
  `towerTensorMap` is the existing `SpTowerGamma.tensorMate`, transported only
  along the compactification equation, and retains its projection and counit.
* The last tower conjunct is the consequence, with `towerGamma` on both sides.
  This is the existing `SpTowerGamma.gamma`, transported only along the
  compactification equation. The right side uses the same tensor comparison
  followed by `(identity,t.hom)` and the primed gamma.
  All three equalities are in `SpTowerShriek.D ... X'.left`, the ordinary derived
  system category equivalent to the original strict-tower derived category.
  They are not assertions only about finite evaluations.

### Dependency declarations read and reused

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
* `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`,
  `SmoothOfRelativeDimension`; the scheme-property convention node introduces
  no competing definition. Separated and finite-type scheme classes are reused.
* `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the standard
  `Limits.pullback` scheme/projection convention (the module's module-base-change
  definition is not the notion of a scheme fibre product).
* `Sheaf.SecSmoothPurity.FiniteGeneralRing` and its reexported data:
  `finiteGeneralRingSmoothPurity`, `FiniteGeneralRingAt`,
  `Etale.FiniteSmoothPurity.OrientationNormalized`, `line`, `gamma`, `comparison`,
  and `IsCtf`. These fix arbitrary-ring orientation and the finite purity maps.
* `Sheaf.Paper.SmoothPurityCoefficientTowers`: `spCoefficientTowers`,
  `spCoefficientRing`, and the quotient-semilinear transitions.
* `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`:
  `SpCoefficientTowersAbelian`, `spCoefficientEvaluation`, and ordinary derived
  evaluation/reduction. `Sheaf.Paper.SmoothPurityNormalizedTowers`:
  `spDerivedCoefficientTowers`, `spConstructibleTorTowers`, and its full category.
* `Sheaf.Paper.DerivedPullbackTensorHom`: its recorded finite pullback/tensor
  convention; the fixed-module presentation uses the actual pro-etale
  `upperStar.leftDerivedFunctor`. The tower operations are the ordinary system
  operations from `SpTowerShriek`, not the completed integral operations.
* `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`:
  `ProEtale.derivedTensor`; `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`
  reexports the finite root/Tate objects; tower `orderedLine` is the published
  shifted tensor-power presentation of those same finite twists.
* `Sheaf.Paper.SmoothPurityTowerShriekLevels`: `SpTowerShriek.tower_shriek_levels`
  and its `Base`, `Operations`, `tensorPullback`, `square`, and ordinary tensor.
* `Sheaf.Paper.CohomologicalSmoothnessFiniteComparison`:
  `finiteComparedTensorClause`, `finiteComparedBaseChangeClause` specify the
  finite etale-origin formulation used here.
* `Sheaf.Paper.CohomologicalSmoothnessTheorem` (through the
  finite and tower dependencies) supplies the canonical finite tensor and
  dualizing base-change conventions. The actual finite arrows used here are
  `Etale.smoothTensorDualityMap`, `rightDerivedUpperShriekBaseChangeMap`,
  `dualizingComplexBaseChangeMap`, `leftDerivedUpperStarTensorIso`, and
  `derivedSquareUpperStarIsoInvApp`. The latter four are exactly the cited
  cohomological-smoothness interface, rather than the returned wrappers.
* `Sheaf.Paper.ExchangeProjectionSuppliedDomains`: the recorded finite
  exchange/projection formulas; these are the ones used by the finite maps
  and `SpTowerShriek.projection`, not separately supplied arbitrary arrows.
* `Sheaf.Paper.SmoothPurityTowerGluing`: `SpTowerGluing.support`, `Levels`,
  `tower_gluing` and its actual restricted adjunction.
* `Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange`:
  `tower_exceptional_base_change` and its reexported `SpTowerMate.Data`,
  `U`, `V`, `beta`, and `mate`.
* `Sheaf.Paper.PurityDiagonalDualizingObject`:
  `PurityFiniteSetting.diagonalDualizingObject` and its unique normalization.
* `Sheaf.Paper.SmoothPurityTowerGamma`: `SpTowerGamma.Purity`, `orientation`,
  `tensorMate`, `gamma`, `orderedLine`, `unit`, `originalUnit`, `exceptional`,
  `source`, `tensorSource`, and its finite `coefficientWord` normalization.
* `Sheaf.Paper.SmoothPurityMap`: `smoothPurityMap`,
  `smoothPurityTensorMap`, and `smoothPurityReassociation` fix the finite
  tensor-form/reassociation convention reused by finite gamma and tower gamma.

Stated proof dependencies are imported without `public`; the scalar/tower
orientation transport node has no Lean module and consequently has no import.
The source proof route has not been changed.

### Edge cases

Checked before writing and again against the complete signatures:

* d=0: the ordered line is the coefficient unit, and all empty tensor powers
  and even shifts are included. There is no positive-dimension hypothesis.
* Empty X, Y, or Y': the scheme classes and IsPullback formulation allow these;
  no nonempty-point or nonempty-scheme hypothesis occurs.
* Identity v and identity f: the same canonical compositors and counit mates
  occur; no inequality or nonidentity restriction excludes either case.
* A the zero ring: only CommRing and Finite are assumed, so this case remains.
* n=1: the finite exponent is positive; tower n=0 denotes its first positive
  exponent. There is no accidentally omitted first quotient.
* Ramified E: the coefficient is ell^(n+1), not a uniformizer exponent silently
  assumed equal to n+1; the published `Base` retains ramification transport.
* Non-normalized towers: K has only the uniform ctf membership property.
* Arbitrary v: no smoothness, flatness, etaleness, or properness of v is imposed.
* Site universes are unchanged: schemes have universe u and coefficient modules
  use u+1; no equality of object and morphism universes is added.

No statement correction or disputed statement was needed.

### Searches

Used the prescribed `msearch.py NB det-sp-purity-bc-factors` wrappers:

* leanfinder: "Smooth purity orientation and exceptional tensor map commute with
  arbitrary base change in derived categories of coefficient towers".
  Eight hits, all unrelated Kahler differential and module tensor base-change
  statements; no matching purity factor theorem.
* loogle: `"purity", "baseChange"`. Zero hits.
* grep: `purity.*baseChange|baseChange.*purity`. Zero Mathlib hits.
* leansearch: "Smooth purity orientation and tensor counit map are compatible
  with arbitrary base change for finite coefficient rings and coefficient
  towers". Eight hits concerning ring smoothness, module scalar extension,
  and stable-under-base-change properties; no matching theorem.
* rg in the read-only `lean/WeilConjectures` and `lean/Sheaf`, for
  `purity.*[Bb]ase[Cc]hange|[Bb]ase[Cc]hange.*[Pp]urity|det-sp-purity-bc-factors`.
  Found source nodes/proof dependencies and the ambient finite coefficient
  base-change theorem. The latter is etale, includes a larger package, and
  has no tower factor statement. Its source wrapper was used in the returned draft; the repair removes that
  import and instead specializes the existing generic source constructors
  recorded by the new definition node.
* Read `WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum`: its
  base-change compatibility is a defining field for a supplied orientation
  datum and supplied comparisons, rather than this theorem for the specified
  diagonal orientation; it does not give the required tensor/tower result.

## Repair of returned delivery 3a6f2ec0dcfb

H2: Removed both imports `Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange`
and `Sheaf.Paper.AmbientDiagonalPurityBaseChange`. No declaration from either
module remains in the statement. Added only the authorized new definition node
`def-pur-purity-base-change-sources` to the item's `stmt_deps`; no old theorem
owner or proof ingredient was added there. Its own dependencies cite the exact
existing owners of the canonical Tate transport and tensor-source constructors.
No source theorem from the trace-formula unit is invoked for the new definition.

H4: Replaced the finite `smoothExceptionalBaseChangeMap` by the component of
`Etale.rightDerivedUpperShriekBaseChangeMap A (IsPullback.of_hasPullback f v)`;
replaced the finite unit map by `Etale.dualizingComplexBaseChangeMap` at that
same square. Both are the mate of inverse compact-support exchange with the
actual compact-support counit; the latter includes the actual unit pullback.
Replaced the former source wrapper by `Etale.leftDerivedUpperStarTensorIso`
followed by `derivedTensor.map` of `Etale.derivedSquareUpperStarIsoInvApp` in
its first variable. This leaves u*omega in the second variable. The gamma
source comparison is the existing `ordinaryFiniteTwistedPullbackComparison`
applied to the inverse square isomorphism and the actual normalized Tate
comparison. Its generic signature permits supplied comparisons; the application
specifies exactly which two canonical comparisons are used. The new node's
statement preserves that distinction.

The finite and tower Tate pullback normalizations now both use the existing
`PurityFiniteSetting.purityTwistTransport` from `VectorPurityNormalization`.
Like the former transport, it is characterized by the inclusion of roots in
G_m and the pure-tensor section equation, so this changes no normalization.
The tower mathematics was accepted in the return and its equations and domain
are preserved.

The sandbox's immutable node fields were compared with the current read-only
main node and are identical; the only field deltas are `lean` and the addition
of the new definition id to `stmt_deps`. No direct Git command was used. The
delivery wrapper performs the current-base commit/rebase bookkeeping.

The previous self-check second reading has been removed. A separately
dispatched read-only worker is providing the actual independent reading required
by the return and authorized by this repair request.

## New nodes

`def-pur-purity-base-change-sources` defines the existing canonical finite Tate
pullback and the existing generic tensor-source comparison, with the precise
canonical specialization used in the item. Its `existing:true` record points
to `Etale.vectorIntegrationBaseCoefficientPullback` in
`Sheaf.AlgebraicGeometry.VectorBundleIntegrationCharts`; that module publicly
exposes the second constructor `Etale.ordinaryFiniteTwistedPullbackComparison`,
defined in `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows`. No Lean declaration
is copied or added. The node cites both constructors' existing general owners,
the normalized transport owner, and the derived coefficient conventions. Its
source is the canonical source-identification sentences of the latest blueprint
factor statement, clauses (1), (2), and the consequence. No purity assertion is
moved into it.

The three new Mathlib searches were actually run through `msearch.py`:
LeanSearch for canonical pullback of finite Tate twists and the tensor source
returned eight generic pullback statements; Loogle on
`leftDerivedUpperStarTensorIso, derivedSquareUpperStarIso` returned zero hits
and an unknown project-identifier diagnostic; Mathlib grep on
`Tate.*[Pp]ullback|[Pp]ullback.*[Tt]wist` returned eight unrelated comments or
pullback statements. Exact project/DAG searches found the two generic owners
and the trace-formula wrapper, but no node giving their finite purity-source
specialization. Blueprint search for "twist pullback" found
`thm-amb-p1-decomposition`; "source identification" included this item's
statement among four matches. `def-pur-section-tate-pullback` is the specialized
pro-etale section-integration construction for `PurityFiniteSetting`, not the
arbitrary-finite-ring ordinary comparison needed here. The search records are
included unchanged in the new node. The canonical constructions are reused.

## Second reading by NB

Independent reader: `NB repair_second_reader`, a separately dispatched read-only worker.
I read the item node, the latest blueprint factor statement, the complete repaired Lean
module, the new `def-pur-purity-base-change-sources` node, and this report. I also opened
the full source signatures and defining formulas of the canonical exceptional/unit
exchanges, tensor/square comparisons, the two existing source constructors,
`purityTwistTransport`, finite gamma, and the published tower gamma data. I made no edits
and ran no Git command or compile.

The repaired statements retain every mathematical hypothesis: the finite-field datum
and distinct coefficient prime, separated finite-type schemes over that field, smooth
separated f of pure dimension d≥0, arbitrary v and its Cartesian square, arbitrary finite
commutative ell-primary A, and all finite extensions E/Q_ell. The extra
Noetherian/compactification/quasi-compactness and Geometry/invertible-exponent arguments
are certificates supplied in this setting. `OrientationNormalized` pins both finite
alpha maps to the specified diagonal/Rees/integration construction. Finite K ranges over
all etale representatives whose comparison images are intrinsic constructible finite-Tor
objects; the equalities themselves lie in the pro-etale derived category. Tower K ranges
over the full uniform ctf category, with no normalization condition.

I checked the three conclusions in both coefficient cases in Lean's left-to-right
composition order. Clause (1) is pulled inverse orientation followed by the unit
exceptional exchange, equal to canonical Tate pullback followed by the primed inverse
orientation. Clause (2) is pulled actual projection/counit tensor transpose followed by
e_K; its other side applies the monoidal/square source comparison, tensors identity with
that same e_1, then applies the primed tensor transpose. The final conjunct is the
analogous equality for the defined gamma composite. The finite
`rightDerivedUpperShriekBaseChangeMap` is exactly the adjunction mate of inverse
compact-support exchange; `dualizingComplexBaseChangeMap` is its unit component followed
by the actual unit comparison. The inline `leftDerivedUpperStarTensorIso` and
`derivedSquareUpperStarIsoInvApp` act in the correct tensor factors. The tower helpers
retain the same original and primed adjunctions at c and c.ofIsPullback sq; they only
transport the published maps through the compactification equation and section-preserving
realization. The tower s/t comparisons are pinned at every positive level by the stated
unit and normalized root-line equations, rather than assumed arbitrary isomorphisms.

The new existing:true definition node introduces no new Lean data or theorem. Its primary
recorded signature matches `vectorIntegrationBaseCoefficientPullback` verbatim, and its
second constructor is the existing scheme-general
`ordinaryFiniteTwistedPullbackComparison`. The node correctly distinguishes arbitrary
supplied e,c in that generic constructor from the item's actual specialization: e is the
inverse canonical derived-square isomorphism, and c is the ordered Tate pullback using
the already owned roots-and-pure-tensor normalized `purityTwistTransport`. Thus it asserts
no missing exceptional/orientation compatibility and uses no trace-formula theorem. Only
this new definition id is added to the item's stmt_deps; the item statement, proof and
proof_deps are unchanged. No `AmbientDiagonalPurity` or former smooth exceptional/base-change
wrapper reference remains in the delivered module.

I checked d=0, empty schemes, identity base change and identity f, the zero coefficient
ring, the first finite/tower level, ramified E and non-normalized input towers. No
hypothesis excludes these cases; tower index n denotes ell^(n+1), and no coefficient or
site universe equality has been imposed. The two named theorem proofs alone use sorry;
all nine helper definitions have real data.

The mismatch found during this independent reading was one stale Searches sentence
saying the ambient source wrapper was still used. It was requested to be corrected to
describe its removal in this repair. The H2/H4 API and ownership corrections are present
in the Lean and node files. I found no remaining mathematical mismatch between the
repaired statements and the node/latest blueprint. Compiler and delivery checks are
performed by the implementing worker, independently of this reading.

### Repair validation

The repaired module passed `scompile.py NB det-sp-purity-bc-factors`, exit 0,
with no warnings or errors. The actual library module compiled in 47.2 seconds;
the wrapper also checked its sandbox presentation and rebuilt the needed live
overlay dependency. No compiler option relaxing transparency was introduced.
The item binding records the repaired signature verbatim, all eleven public
declarations are listed, and no Lean source line exceeds 100 characters.
The new node is existing:true and adds no file to compile.
