## Worker report

The helper definitions are stated for generic finite-extension coefficients at
zero-based level n; the main definition specializes them to the fixed purity
setting at P.level-1. Generic projection helpers require the coefficient prime
to be invertible on the base; the main definition derives this from the setting.

The delivery has three modules. `AffineLinePurityCoordinateMaps` owns the
canonical coordinate-operation templates; `AffineLinePuritySource` owns the
twisted source and explicit bounded origin.
`Sheaf.Paper.AffineLinePurityComparison` defines the affine-line
integration map, the symmetry-adjusted inverse projection map Pi_K, their tensor
composite a_K, and gamma_{p,K} as the existing specified-class Hom transpose of a_K.
All definitions contain real canonical constructions. The postponed propositions
are boundedness, projection invertibility and prime invertibility used
in the node, together with the named defining-equality obligations; each has a
proof description.

Clause-by-clause correspondence:

- `P : WeilConjectures.PurityFiniteSetting` retains the algebraic closure of the
  finite field, its characteristic, the distinct coefficient prime, the fixed
  coefficient closure, the finite intermediate extension E, and positive level n.
  `Ring P` abbreviates the EXISTING `Scheme.finiteTateCoefficient` at index n-1.
  That API uses exponent index+1. Positivity gives (n-1)+1=n, so this is exactly
  the standard size lift of O_E/varpi_E^n, including n=1. No divisibility by the
  ramification index is assumed. `coefficientFinite` uses the existing finiteness theorem. `ringEquiv` gives
  the canonical reindexing ring isomorphism to `P.Coefficient`.
- `Y : Scheme`, `aY : Y ⟶ Spec (.of P.field.k)`, and instances
  `LocallyOfFiniteType aY`, `QuasiCompact aY`, `IsSeparated aY` say separated finite
  type over k. The explicit structure map is also required by the recorded
  finite-type/Noetherian declaration.
- X is `AffineSpace PUnit Y`, p its existing structural morphism. P is the existing
  `ProjectiveLine Y`, q its structural morphism. `ProjectiveLine.affineChart Y`
  is the existing D_+(T_1) immersion t=T_0/T_1. The actual chosen compactification
  is `affineTraceLineCompactification Y`, whose open and proper maps are these j,q.
  Its structure retains qj=p and properness. The main body derives Noetherian Y
  by `isNoetherian_of_locallyOfFiniteType aY`; the standard affine/projective
  geometry gives the remaining quasi-compactness instances. The existing Hom
  equivalence implements the finite-amplitude argument, rather than accepting a
  dimension bound as extra input.
- C_T is `VectorIntegrationSite.comparison (Ring P) T`, the existing exact
  derived comparison pullback, with the existing comparison morphism.
- `r : Nat` and `hA : (ell^(r+1) : Ring P)=0` encode the node's arbitrary positive
  annihilating exponent r_node=r+1. This includes every r_node>=1.
  `linePlus` uses the existing ordinary finite roots-of-unity Tate line in
  degree -2. `etaleCoefficient` is j_e^* B_P[2], identified with B_X[2] by the
  existing canonical root pullback. `coefficient` is its comparison image.
  `coefficientTwistIso` explicitly identifies it with the prescribed
  `Scheme.finiteTateProSheaf ... X 1` placed in degree zero and shifted by two,
  using ordinary shifted Tate pullback and `VectorIntegrationSite.twistDerived`.
  Thus the coordinate presentation uses the recorded tau, not a new Tate twist.
- `integration` specializes the real helper `restrictTrace` to the normalized
  projective trace. That helper first applies the canonical site/inverse-image comparison and
  then Rq_* of `(openAdjunction ... j).counit.app L`. It finally applies the
  existing `projectiveTrace`, normalized as the second projection of the inverse
  projective-line decomposition. The dependency's projectiveComparison theorem
  identifies this with C_Y(t_q^e) beta_q^{-1}. It is the actual counit, not an
  unspecified arrow of the same type.
- The main K is an actual pro-etale bounded-below object, not a literal comparison
  image. `Ke`, `hKe : Etale.DerivedCategory.constructibleFiniteTor ... Ke`, and
  `eK : C_Y Ke ≅ K.obj` are the representative explicitly chosen in the node.
  They parameterize the node's choice; finiteTorComparisonNoetherian ensures
  every pro-etale D^b_ctf object has such inputs. No arbitrary Nonempty choice is
  used to construct data. The resulting formula applies to arbitrary K and iso eK.
- `source` is literally `Lp^*K tensor coefficient`; `etaleSource` is
  `p_e^*Ke tensor etaleCoefficient`. `sourceComparison` composes the canonical
  tensor/pullback comparison with the derived pullback of eK. `etaleSource_plus`
  and `source_plus` retain the asserted bounded-below properties; `sourceWitness`
  stores precisely that explicit ordinary complex and canonical isomorphism.
- `projection_isIso` is the finite compact projection assertion specialized to
  this coefficient, Ke, eK and the literal compactification. `projectionIso`
  inverts the existing `VectorIntegrationSite.projection` using this proof.
  That projection is the composite symmetry on Y, canonical PF, then Rp_! of
  symmetry on X. Its inverse therefore has exactly the order specified for Pi_K:
  Rp_!(s_{p^*K,F}), PF^{-1}, s_{Rp_!F,K}.
- `augmentation` is `projectionIso.hom` followed by tensor with `integration`
  and the coefficient right unitor. The unitor helpers use the existing exact
  strong-monoidal comparison and the native derived monoidal right unitor;
  they do not use Ke or eK. Representative data enter only the proof that PF is
  invertible, not the arrow being inverted or the tensor/unitor formulas.
- `ordinaryLeftAdjoint` supplies the already proved ordinary etale adjoint
  instance at this compactification. The main definition applies exactly
  `specifiedExceptionalHomEquiv` to `augmentation`, with `sourceWitness` and K.
  Its target is `(sfFiniteExceptionalAt (Ring P) c).obj K.obj`. That existing
  functor is the specified ordinary exceptional functor conjugated by comparison.
  The Hom equivalence is the normalized four-Hom chain with the explicit origin.
  It is not an assumption of an adjunction on all pro-etale complexes. Witness
  coordinates enter only this canonical chain's applicability; they do not
  replace any of the integration or projection arrows. No IsIso of gamma is stated.

Dependency interfaces read and used (transitive canonical helpers are reexports
of the directly imported statement dependencies):

| Module | Declaration / role |
| --- | --- |
| Sheaf.Paper.PurityFiniteSetting | WeilConjectures.PurityFiniteSetting; coefficientPrime_isUnit_stalk |
| Mathlib.AlgebraicGeometry.AffineSpace | AlgebraicGeometry.AffineSpace and structural projection |
| WeilConjectures.AlgebraicGeometry.ProjectiveSpace | ProjectiveSpace, over, proper instance |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts | projectiveSpace_standardCharts |
| Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed | siteComparisonDerivedPullbackPlus |
| Sheaf.AlgebraicGeometry.ProEtaleSiteComparison | Scheme.proEtaleSiteComparison |
| Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted | existing finite coefficient twists reexported |
| Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback | Scheme.etaleFiniteTwistPullback |
| Sheaf.Paper.VectorIntegrationSiteComparison | VectorIntegrationSite.finiteTypeSiteComparison, projectiveComparison |
| Sheaf.AlgebraicGeometry.ProjectiveLineTrace | Etale.projectiveLineTrace, projectiveLineTraceTransport |
| Sheaf.AlgebraicGeometry.ProEtaleExtensionZero | actual derived open-extension adjunction |
| Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport | compactification compact-support construction |
| Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian | finiteTorComparisonNoetherian |
| Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses | canonical derived tensor comparison |
| Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence | supportSiteComparison_pullback_coherent |
| Sheaf.Paper.ExchangeProjectionSuppliedDomains | supplied-domain canonical projection interfaces |
| Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula | Etale.isIso_finiteCompactProjection |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | finite exceptional adjunction interfaces |
| Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom | specifiedExceptionalHomEquiv |
| Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt | sfFiniteExceptionalAt |
| Mathlib.AlgebraicGeometry.Morphisms.FiniteType | isNoetherian_of_locallyOfFiniteType |
| WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType | exists_topologicalKrullDim_le |
| Sheaf.Paper.DerivedPullbackTensorHom | existing derived operations reexported |
| Sheaf.Paper.FiniteSiteCoordinates | comparison, unit, line, linePlus, pullback, twistDerived |
| Sheaf.Paper.FiniteSiteTensorProjection | projection, tensorPullbackComparison |
| Sheaf.Paper.ProEtaleProjectiveLineTrace | projectiveTrace |
| Sheaf.Paper.ProEtaleAffineLineCounit | lineLeft, openAdjunction |
| Sheaf.AlgebraicGeometry.AffineTraceTower | affineTraceLineCompactification |
| Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness | Scheme.FixedEtaleOriginWitness |

Edge cases checked against the definitions: the empty scheme satisfies the germ
criterion and has the same literal chart compactification; n=1 corresponds to
Tate index zero; arbitrary ramification and positive level are retained; all
positive annihilating exponents are allowed; K=0 and complexes with negative
cohomology are allowed; K need not be definitionally C Ke; the small pro-etale
site keeps object universe u+1 and morphism universe u. No unrelated site universe
is equated to another and no projective-space coordinate chart is substituted.

Searches for an existing definition:

- msearch.py LeanFinder: affine line purity comparison exceptional adjoint compact
  support integration projective line trace; 8 unrelated hits, no such construction.
- msearch.py Loogle: CategoryTheory.Adjunction.homEquiv; generic adjunction results,
  no geometry or affine-line comparison.
- msearch.py grep: affineLinePurity|affineLineIntegration|purityComparison; no hits.
- msearch.py LeanSearch: affine line purity comparison from compact support
  integration and the exceptional inverse image; 8 unrelated integration/affine hits.
- rg in lean/WeilConjectures and lean/Sheaf for the desired construction names:
  no exact existing definition. Searching the node id finds the upstream smooth
  purity file's explicit note that this canonical comparison is not constructed;
  its existence-only result does not define the node's arrow.
- Source and DAG dependencies were read before selecting the canonical chart,
  trace, projection and specified exceptional-Hom interfaces above.

No statement correction, disputed statement, or dependency record repair is
proposed. Two new definition nodes own the helper coordinate operations and
retained bounded source that the comparison uses.

## Second reading by NI

The dispatcher requires a single worker and forbids starting another agent. This
is a separate sequential rereading by NI, not a claim of independent-agent review;
the maintainer supplies the independent review. The node and module were compared
clause by clause. This found the positive versus zero-based coefficient indexing
and corrected the call sites to n-1. It also checked the order of the two tensor
symmetries, the literal extension-by-zero counit, the arbitrary pro-etale target
K with explicit eK, and the specified compactification in both compact support
and the exceptional target. The native right unitor was chosen to keep its formula
independent of the representative.

## New nodes

`def-pur-affine-line-purity-coordinate-maps`, module
`Sheaf.Paper.AffineLinePurityCoordinateMaps`, supplies the canonical comparison
unit and right unitor, tensor-trace composition, actual open-counit restriction,
and arbitrary-realization tensor/pullback comparison. It also supplies the
normalized shifted finite-Tate pullback comparison. These are explicit composites
of the existing dependency maps. The source is the coordinate-identification and
integration displays of main-20261015 order 2318. Its LeanSearch query for the
combined derived source/witness returned 8 ordinary etale and algebraic results;
LeanFinder for the coordinate trace/tensor maps returned 8 unrelated profinite
projection results; the Mathlib grep for the new construction names returned zero.
Project and DAG searches found the component APIs already reused here, but no
such combined arbitrary-realization construction. The node records these queries
and results, and cites every component's existing node. Arbitrary trace and
realization inputs are arguments to the generic compositional helpers; the main
node supplies the actual normalized trace and the actual canonical projection,
so no arbitrary map replaces the map specified in the source.

`def-pur-affine-line-purity-source`, module
`Sheaf.Paper.AffineLinePuritySource`, supplies the compared shifted Tate
coefficient, its canonical inverse-limit identification, M_K, its displayed
ordinary representative, the canonical source comparison and the retained bounded
origin. Its two boundedness theorems state exactly the lower-bound assertions in
this new node and in the original item. Five additional named theorems retain
the defining coordinate equalities of the actual objects, so equality transports
avoid repeatedly unfolding large categorical instances. They assert only the
defining equalities, with reflexivity proof plans. Every proof is postponed, and
every definition still contains its actual data; their docstrings give the proofs. The
source is the explicit etale-origin display of the same blueprint paragraph.
The same three kinds of search and additional DAG/blueprint searches found no
existing declaration that retains this arbitrary actual pro-etale K, its chosen
eK and this tensor-origin construction; existing general witness and tensor
comparison definitions are reused. It depends on the coordinate-map node; the
original item gains only this source node in stmt_deps. Every new module and
named declaration has a unique owning node and its corresponding blueprint tag.

The second reading also checked these new statements against their modules:
coordinate maps contain real data, finite quotients use the existing coefficient
construction, the source witness stores the specified ordinary tensor complex,
and the new dependency path is acyclic.

The coordinate-map module also publishes the standard Ring instance induced by
the existing quotient CommRing instance. This canonical structure cache aligns
specialized ModuleCat arguments with the generic APIs; it adds no ring data.
The defining coordinate equalities are retained as named proof obligations,
with explicit equality transports between the already constructed objects.

The coordinate operations include the ordinary and pro-etale tensor-source objects
used on both sides of the realization comparison, the module-coefficient right
unitor and tensor trace, and the inverse of the actual canonical projection with
its IsIso proof. The source module specializes these shared object constructions;
the parent specializes these shared arrow constructions. Their data are exactly
the displayed pullback/tensor objects and inverse/trace composites, respectively.

For Pi_K the shared projection-source object is literally p^*K tensor F, and the
shared projection-target object is literally K tensor Rp_!F. The source alias,
the inverse canonical projection and the tensor trace all use this same literal
source object. Thus the specialized projection is a direct application of the
canonical inverse and augmentation a direct application of inverse projection,
tensor integration and the coefficient right unitor. No auxiliary source
transport is needed at this stage.

The map module also names `ProjectionInvertible`, definitionally exactly `IsIso`
of the specified symmetry-adjusted canonical projection transformation. This
shared predicate prevents a repeated specialized type check; it adds no
mathematical hypothesis. `projection_isIso` states this exact predicate, and
`inverseProjection` unfolds it to invert the actual canonical map. The local
specializations `projectionIso` and `augmentation` infer their return types from
these generic constructions.

Validation: all three delivered files compiled cleanly with `scompile.py`, both
as sandbox files and under their library module names. The library-name checks
took 25.4, 15.0 and 10.8 seconds for the coordinate, source and comparison
modules respectively. No development tracing or diagnostic commands occur in
the delivered files.
