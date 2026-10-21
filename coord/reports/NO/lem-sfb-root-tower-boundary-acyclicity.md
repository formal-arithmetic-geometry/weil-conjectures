## Worker report

The item is stated in `Sheaf.Paper.RootTowerBoundaryAcyclicity`, declaration
`AlgebraicGeometry.ProEtale.RootBoundary.rootTower_boundary_acyclicity`. Its proof is
`sorry`. The original statement, source, proof and proof dependencies are unchanged;
only its Lean record and three additional statement dependencies are delivered.
This is stage 2, not another split of NI's already reviewed stage-1 proof.

The conclusion gives the normalized isomorphism in the ordinary unbounded derived
category for both E and the normed algebraic closure, together with explicit
naturality and scalar-restriction diagrams. It is not a per-degree replacement for
a derived isomorphism. Definitions have actual data and every postponed proof is a
named theorem with a proof docstring in the module owned by its definition node.

### Hypothesis correspondence

- Distinct primes: `p ℓ`, `[Fact p.Prime]`, `[Fact ℓ.Prime]`, `hpℓ : p ≠ ℓ`.
- Base field and characteristic: `k`, `[Field k]`, `[CharP k p]`.
- Norm-topological finite extension: `E`, `[NormedField E]`,
  `[NormedAlgebra ℚ_[ℓ] E]`, `[FiniteDimensional ℚ_[ℓ] E]`.
- Algebraic closure with its extended norm: `Ω`, `[NormedField Ω]`,
  `[NormedAlgebra E Ω]`, `[IsAlgClosure E Ω]`. No completeness hypothesis.
- Regular separated finite-type scheme: `Y`, `y : Y ⟶ Spec (.of k)`,
  `hY : IsRegularScheme Y`, `[LocallyOfFiniteType y]`, `[QuasiCompact y]`,
  `[IsSeparated y]`. The first two morphism conditions together say finite type.
- Affine etale chart: `A`, `[CommRing A]`, `b : Spec (.of A) ⟶ Y`, `[Etale b]`.
- Exactly the SNC branches in the chart: `r`, `s : Fin r → A`, `H`,
  `hH : IsStrictNormalCrossingsBoundary H`, `hproduct` identifies H with the
  ideal sheaf of the product of the parameters, and `hbranches` identifies their
  zero loci with exactly the irreducible components of the boundary support.
- Affine pro-etale base: `R`, `[CommRing R]`, `a : A →+* R` and
  `[WeaklyEtale (Spec.map (CommRingCat.ofHom a))]`, using precisely the weakly-etale
  small-site convention of the recorded `Scheme.ProEt` dependency.
- Finite-dimensional boundary vector space: inside `Assertion`, `M : Type u`,
  `[AddCommGroup M]`, `[Module E M]`, `[FiniteDimensional E M]`.
- Supplied finite-rank lisse extension: `N : SiteMod F (tower p t)` and
  `IsLisseCoefficientModule (coefficients F) N` inside `Assertion`.
- Supplied, rather than existentially replaced, boundary identification:
  `e : (CondensedRing.upperStar ... (boundary p t)).obj N ≅
  (pointPull F (stratumScheme t)).obj (model F E M)`.
- Every profinite parameter: `∀ P : Profinite.{u}`. A single common containing
  universe u contains the rings, schemes and arbitrary parameter sets; the site
  has the upstream object/morphism size convention and coefficients are Ab.{u+1}.
  No equality between the site's object and morphism universes is imposed.

### Objects and conclusion correspondence

- `coefficients F` is the existing `Profinite.continuousCoefficientRingObj F`.
  Its sections are all continuous maps; the recorded universe-generalized
  continuous-map ring agrees with this same-universe specialization. Neither
  locally constant functions nor finite-subextension-valued functions are used.
- `SiteMod`, `PointMod`, `pointPull`, `pullD`, and `pushD` are explicit aliases or
  specializations of the recorded internal modules and derived pushpull.
- `tower p t` uses the existing `tameRootAlgebra p t`: generators for every positive
  prime-to-p order, power relations, and the divisibility transition relations.
  This presentation is the specified filtered colimit, not unrelated nth roots.
- `puncture` uses the existing product-inverting `parameterRootOpen`; `qP`, `vP`
  and `jP` are the actual structural morphisms on actual profinite test schemes.
- `stratumRing t = R ⧸ Ideal.span (Set.range t)`, `stratumScheme`, and
  `stratumInclusion` represent S and s. `zeroRoots` is a real quotient lift,
  whose defining relations vanish by the named theorem `roots_vanish`;
  `boundary` is its Spec map and represents i.
- `model F E M` is the condensation of `F ⊗[E] M` with `moduleTopology`.
  In finite dimension this is the finite product norm topology even for
  incomplete Ω. The reused condensation theorem characterizes sections,
  restrictions, scalar actions and maps; its universal characterization
  determines the object up to the canonical isomorphism used downstream.
  The choice of that characterized functor is not a choice from bare existence.
- `freeParameter F P` reuses `CondensedBar.freeParameter`, built by sheafified
  free abelian groups followed by the internal free-module adjoint. Thus it is
  free on the represented condensed set, not the free module on the underlying
  discrete set. `parameterFunctions` right-derives internal Hom in its value
  argument, with ordinary unbounded derived categories.
- `testModule` pulls N[0] exactly to T[P]. `openSource` is exactly
  s^* Rv_{P,*}(N restricted to T-circ[P] [0]); exact pullback commutes with the
  degree-zero embedding. `target` is exactly p_S^* RHom(C_F[P],M_F[0]).
- `NormalizedComparison` explicitly asserts an isomorphism `α` between those
  derived objects. It also identifies the actual open-unit map `lambda` and
  parameter evaluation `beta` as isomorphisms and requires
  `lambda ≫ α.hom ≫ beta = fullRestriction`. These are the very canonical
  maps in the node's reviewed proof, not arbitrary witnesses for the objects.
- `fullRestriction` is the actual exchange adjunct along the zero-root boundary
  followed by the supplied e. `derivedEvaluation` specializes the recorded
  `ProfiniteFunctions.comparison`, constructed from the
  tautological parameter generator, actual diagonal, internal tensor-Hom
  evaluation, ordinary adjunction, then universal right-derived descent.
  In particular its data are not chosen by an existence theorem about isomorphisms.
- The degree-zero normalization is expressed by this equality of derived arrows:
  applying H^0 gives restriction of actual full-tower sections to S[P], followed
  by their exponential-law interpretation as functions of P. At P=* evaluation
  is the identity under the canonical one-point identifications; the full-source
  exchange is the inverse of the pullback-adjunction unit by its triangle
  identities. The same equality therefore identifies α_* with the inverse of
  the puncture unit, under the canonical full-source/boundary identification.
- `ModuleNaturality` is the explicit square for f:N→N' and g:B→B' respecting
  the supplied e. `ParameterNaturality` is the square for every continuous
  P'→P; its source map is actual section restriction and its target map is
  derived precomposition on the existing free modules.
- `FamilyNaturality` quantifies over commuting maps of full, open and boundary
  test schemes over a pro-etale base map and an actual derived full-module arrow.
  `familyOpenMap` and `familyBoundaryMap` are induced from that same arrow.
  `sourceBaseChange` is the actual exchange on punctured direct images and
  `parameterTargetTransport` is actual exchange transported through evaluation.
  Taking the entire base U[Q], its actual full-tower automorphism and supplied
  equivariant module arrow gives equality on the Q-parametrized terms.
  There is no pointwise hypothesis or pointwise-only conclusion. The identity
  base and inverse tower automorphisms give the ordinary equivariance clause.
- `ScalarCompatibility p t E Ω` quantifies over exactly a finite-dimensional E-space
  M, a supplied lisse E-extension N, its supplied boundary identification e, every P,
  and the two normalized isomorphisms. Its Omega-model is literally `model Ω E M`.
  The Omega identification has exactly this model as codomain and satisfies
  `IsScalarExtendedBoundary`: its restriction along the actual pulled ordinary
  tensor unit equals e followed by point pullback of `scalarModelMapD`.
  This is the exact ordinary tensor-unit equation, embedded in degree zero with
  the canonical exact restriction comparisons. The degree-zero embedding is
  fully faithful, so the equation determines the ordinary identification itself;
  it is not merely equality after taking cohomology. This is the ordinary
  extension/restriction adjunction's exact characterization of the scalar extension
  of e followed by the canonical model identification. It is not an arbitrary
  B' or e'. `scalarBoundaryIdentification_existsUnique` asserts there is exactly
  one such identification and gives its constructive proof using
  `CondensedRing.pullIso`, ordinary extension of e and the finite-free
  continuous-model identification.
  Thus the interface includes existence and uniqueness; its compatibility clause
  is not vacuous and adds no restriction on the supplied E data. The model adjunct
  is invertible because a finite basis identifies ordinary tensor extension with
  a finite sum of regular modules; this construction is the proof recorded in
  the existence-and-uniqueness theorem's docstring.
- `scalarModelMap` transports the library's `ProfiniteFunctions.scalarConstantMap`
  along `modelIso`, whose unique sectionwise identity characterization prevents any
  arbitrary choice. Thus the target model arrow really is M_E → Res M_Omega,
  sending m to 1 tensor m. `scalarModelMapD` includes the exact single-complex
  restriction identification; `scalarTargetUnit` applies derived internal Hom
  to that arrow. `scalarTargetRestriction` reuses the library's `restrictHomD`
  after the inverse point-pullback/restriction identification.
- `scalarCommonTarget` is p_S^* RHom_E(C_E[P],Res(M_Omega[0])). Both target maps
  land there, then `scalarCommonEvaluation` lands in its actual parameter direct
  image D. The single equation defining `ScalarCompatibility` contains both
  alpha_E and alpha_Omega and has codomain D. Its domain is the biproduct of
  the full E source A and the scalar-restricted full Omega source B. The
  biproduct's universal property says exactly that both legs of the canonical
  cospan A → C ← B commute with the two target maps and `scalarCommonBoundary`.
  The A leg is `fullOnMap` of `scalarTestUnit`; the B leg is
  `scalarFullRestriction`, using `restrictPull.hom` then `restrictPush` in their
  canonical directions. The common boundary arrow uses exchange on Res N_Omega,
  inverse pullback/restriction, and exactly the pullback of e_Omega. Therefore
  the two alpha maps meet the same restricted Omega-model through the actual
  tensor unit, rather than two unrelated naturality statements. No directional
  direct-image comparison is inverted, and none is assumed invertible.
- This is one root-tower term; no invariants or total nerve object occurs.

### Dependency declarations used

| Module | Declarations and use |
| --- | --- |
| `Sheaf.Topology.ContinuousMapCondensedRing` and `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing` | `Profinite.continuousMapRingObjOfUniverse`, `continuousCoefficientRingObj`: actual all-continuous coefficient ring |
| `Sheaf.Topology.ContinuousMapCondensedRingMap` | `Profinite.continuousMapRingObjMapOfUniverse`, `continuousMapRingSheafMapOfUniverse`: actual coefficient inclusion |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic` | `condensedRingObj`, `coefficientRing`, `profiniteToProEtOf`, `upperStarFromPoint`: coefficients, tests and point pullback |
| `Mathlib.CategoryTheory.Monoidal.Mod` | `CategoryTheory.Mod`: internal modules |
| `Sheaf.Paper.CondensedModuleDerivedPushpull` | `CondensedRing.moduleObjectDerivedPushforward`, `derivedUpperStarLowerStarAdjunction`, `leftDerivedUpperStarIsoMapDerivedCategory`: unbounded derived functors and canonical adjunction |
| `Mathlib.AlgebraicGeometry.Sites.Proetale` | `Scheme.ProEt`, `ProEt.topology`: actual small site |
| `Sheaf.AlgebraicGeometry.IsRegularScheme` | `IsRegularScheme`: the recorded regular-scheme notion |
| `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary` | `IsStrictNormalCrossingsBoundary`: recorded SNC notion |
| `Sheaf.Paper.CoefficientHeartStratificationDefs` | `IsLisseCoefficientModule`: finite locally free coefficient modules |
| `Sheaf.Paper.StrictLocalKummerTameModule` | `TameRootOrder`, `tameRootRelations`, `tameRootAlgebra`: reused compatible root presentation |
| `Sheaf.Paper.RootTowerLisseMorphismExtension` | `parameterRootOpen`, `parameterRootProjection`: reused open and projection only, not that module's morphism-extension theorem |
| `Sheaf.Paper.RootTowerCoordinateFace` | `RootCoordinateFace.testMap`, `squareUpper`, `exchange`: existing generic maps and actual adjunction mates, not its coordinate-face theorem |
| `Sheaf.CategoryTheory.CondensedEquivariantBarData` | `CondensedBar.freeParameter`: existing free internal module, not its bar or invariants assertions |
| `Sheaf.Topology.TopologicalModuleCondensation` | `Profinite.topologicalModule_condensation`: fully characterized continuous-functions condensation |
| `Sheaf.Paper.ProfinitePointPullback` | `profinite_point_pullback`: exact point pullback and canonical coefficient identification |
| `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars` | `Mod.extendScalars`, `comap`, `extendRestrictAdjunction`: ordinary tensor and its actual unit |
| `Sheaf.Paper.ProfiniteConstantDerivedFunctions` | `constantModel`, `modelSection`, `scalarConstantMap`, `restrictPointPullD`, `restrictHomD`: recorded continuous models and actual scalar restriction on derived internal functions |
| `Sheaf.Paper.IntegralLisseClosedBaseChange` | `restrict`, `restrictPull`, `restrictPush`, `scalarUnit`: canonical directional scalar interface; its theorem is also retained as an original proof dependency |

All already recorded proof-dependency modules, including newly landed coordinate
support and integral lisse exchange, are plain-imported in the item's module.
Mathlib monic-root and finite-implies-integral leaves are imported at their recorded
locations. The profinite-constant-functions theorem is now recorded in
`Sheaf.Paper.ProfiniteConstantDerivedFunctions`; its scalar maps are reused, and
its module is also imported as an original proof dependency. Its generic
`comparisonApp` is the component of its recorded `comparison`; the root
helper now specializes that existing natural transformation, keeping the
previously reviewed root interface.
The scalar module uses the existing `scalarConstantMap`, `restrictPointPullD`
and `restrictHomD`, rather than defining a second scalar-functions map.

### Edge cases checked

- r=0: `Ideal.span (Set.range t)=0`, the root presentation has no variables,
  the product is 1, the open is the full tower, and all schemes canonically
  identify with U. No positive-r assumption occurs.
- P empty: the actual test scheme is empty, the free parameter module is zero,
  and the direct image and RHom targets are zero.
- P one point: free parameter is the coefficient regular module; evaluation is
  the normalized identity. This checks the direction of the displayed comparison.
- Finite P: the formula gives a finite product, with no inverse-limit claim.
- Rank zero, zero ring, empty chart or empty stratum: the corresponding derived
  modules are zero and all maps have the required zero interpretation.
- Incomplete Ω: only NormedField, NormedAlgebra and IsAlgClosure are assumed.
  No completion, finite-subextension factorization or scalar flatness is asserted.
- Nonreduced closed full-tower fibre: the proof docstring uses surjective closed
  topological invariance and never identifies that fibre as the scheme S[P].
- Continuous Q-families: tested at the diagram level on the entire U[Q] base,
  not reduced to separate evaluations at points of Q.

### Searches

The search calls are preserved in `mathlib_searches` of each new node with the
actual returned names and digests. The relevant calls were:

- LeanFinder: “Derived sections of a tame root tower with profinite parameters
  and lisse condensed coefficients”: 8 hits (profinite solid/free and BDeRham
  material), no geometric boundary comparison.
- Loogle: `"Kummer", "Hom"`: 0; `"ihom", "Profinite"`: 0.
- Mathlib grep: `([Rr]oot[Tt]ower|[Kk]ummer|profiniteFree)`: 25 hits,
  mainly Kummer-Dedekind and condensed free/solid modules, no exact statement.
- LeanSearch: “Derived evaluation of functions in an internal module on a
  profinite parameter using the tautological section”: 8 hits, including scheme
  evaluation, ordinary sections and ordinary evaluation; none constructs beta.
- LeanFinder: “Canonical derived evaluation of internal module functions on a
  profinite parameter after pullback to a scheme”: 8 light-condensed or sheaf
  restriction hits, no such derived map.
- LeanSearch: “Canonical normalized boundary comparison for compatible Kummer
  roots as boundary exchange composed with inverse open unit”: 8 algebraic-root
  hits, none matches.
- LeanFinder: “Restriction of scalars compatibility of normalized root tower
  boundary comparison using the ordinary extension unit”: 8 algebraic
  restriction hits, no geometric derived comparison.
- Mathlib grep `derivedEvaluation|parameterEvaluation|tautologicalElement` in
  CategoryTheory: 0; grep `root.*[Bb]oundary|[Bb]oundary.*root|scalarPush`: 0.
- Project/source grep for the new namespace and maps: no exact match;
  `TameRootBoundaryMatrix`, `TameRootBoundaryModuleData`, `TameRootBoundaryData`
  are existing strict-local matrix-data structures, not these relative derived
  arrows. The existing compatible-root, free-module and test constructions
  found in the search are explicitly reused.
- DAG id search: no new id already exists. Blueprint searches “root tower”,
  “derived profinite evaluation”, “normalized root boundary”: 0 matches.
  `blueprint_refs.py ancestor` reports the already recorded null ancestor.

Repair searches: LeanFinder “Restriction of scalars on derived internal functions
of a profinite parameter, compatible with the map M to Omega tensor M” returned
8 hits (condensed free/solid objects and ordinary module restriction); Loogle
`"ihom", "comap"` returned 0; Mathlib CategoryTheory grep
`restrictHomD|scalarConstantMap|scalarBoundaryIdentification` returned 0.
Project grep found the now-recorded profinite-functions scalar maps; their full
signatures and docstrings were read and their existing declarations are used.
The new scalar definition node records these actual results and the sectionwise
identity needed to relate the two existing continuous-model presentations.

No statement correction or STATEMENT-DISPUTED flag is needed. The source paragraph
(3) supplies the open-image preservation context; this node explicitly labels the
all-continuous root calculation as an agent-formulated input. This delivery does
not claim to prove that analytical input or to derive it from finite coefficients.

## New nodes

`def-sfb-derived-profinite-evaluation` owns `ProfiniteDerivedEvaluation.lean`.
It supplies the root interface to the actual evaluation transformation and the
recorded `ProfiniteFunctions.comparison` (derived evaluation followed by its
canonical projection adjunct),
the continuous finite-dimensional boundary model, and section/parameter maps.
The retained ordinary-evaluation helpers construct the universal generator,
diagonal and adjunct. Their named naturality theorem has its complete adjunction
proof in its docstring. The derived comparison itself is reused from the recorded
library module.
Its source is the canonical parameter-functions arrow in paragraph (3)'s agent
expansion. The repair's current-library search found the recorded comparison, and
`derivedEvaluation` now specializes that existing map directly. The retained
module also supplies the root-specific condensation-model and section interfaces;
no second derived comparison is constructed.

`def-sfb-root-boundary-comparison` owns `RootBoundaryComparison.lean`.
It supplies the actual zero-root boundary, its defining commutative squares,
the normalizing equation and the precise naturality diagrams. The named
postponed elementary proofs establish the quotient map and commuting squares;
the node explicitly includes those properties, and each has its complete
natural-language proof. Generic naturality is a proposition definition, not an
extra theorem or a copy of another node's geometric assertion. Existing root
and generic exchange operations are used, as the searches require.

`def-sfb-root-boundary-scalar-comparison` owns
`RootBoundaryScalarComparison.lean`. Its statement is rewritten to specify
finite-dimensional M, the fixed model M_Omega, the ordinary scalar extension
of the supplied e, the actual target model map, and the single common-codomain
cospan equation. It cites the now-recorded profinite-functions node for its
existing scalar maps, and the condensation node for the sectionwise model
identity. The new named helper theorems are `modelIso_existsUnique` (the
identity on all continuous sections, hence unique) and
`scalarBoundaryIdentification_existsUnique` (the actual tensor-unit equation,
whose uniqueness is the extension/restriction adjunction).
Their complete proofs are recorded in their docstrings and in this new node's
statement. All definition data are compositions, actual adjuncts, or the uniquely
sectionwise characterized identity of model presentations. The boundary
scalar datum is specified by its actual unit equation and its named
existence-and-uniqueness theorem. No independent analytical comparison is
postponed in these helpers. The search on the current library found the
profinite-functions scalar maps and they are reused; no existing node supplies
the root-boundary cospan equation with the scalar-extended supplied e.

All three nodes retain the exact null blueprint ancestor and prepend this item
to the existing via chain; they cite their existing building notions explicitly.
No dependency node or live library module is modified. The retained profinite-evaluation
module imports the now-recorded profinite-functions infrastructure so that the
shared monoidal module structures are used consistently by its scalar consumer.

## Second reading by NO

This is a fresh reading of the retained item, all three new-node statements,
and the final four modules against the returned head fc3955febca9. The
item's source statement, geometric hypotheses and proof dependencies remain
unchanged. The dispatcher explicitly prohibits starting another agent; this
section records my separate self-check, and does not claim an external review.

H3: the returned definition quantified over unrelated B' and e'. I checked
`ScalarCompatibility`: its Omega target is now exactly `model Ω E M`, and
`Normalization Ω` receives the supplied e_Omega with exactly that codomain.
`IsScalarExtendedBoundary` requires its tensor-unit adjunct to be e followed
by the actual point-model unit. The extension/restriction adjunction says
this is precisely the scalar extension of e and the canonical model map,
not a stronger compatibility assumption or an arbitrary identification.
The named existence-and-uniqueness theorem constructs this very isomorphism
from `CondensedRing.pullIso`, ordinary extension of e and the invertible
finite-free model adjunct. Consequently the quantification is exactly over
the canonical scalar-extended data; no case of the item is discarded.
`modelIso_existsUnique` specifies equality on every profinite section and
`scalarModelMap` reuses `ProfiniteFunctions.scalarConstantMap`, so its map is
precisely m ↦ 1 tensor m. `scalarTargetUnit` is RHom applied to this map;
`scalarTargetRestriction` uses `restrictHomD`, rather than undoing both
trivializations and losing the target map. In the defining biproduct equation,
the first component contains alpha_E and the second contains restricted
alpha_Omega; both land via the actual target maps and evaluation in D. On the
right, both source components land in the same C before its actual exchange
and the scalar-extended e. Precomposing with each biproduct inclusion gives
exactly the two legs of this one common cospan equation, with no arbitrary
lift or missing existence hypothesis. Conversely those two legs imply the
single equation by the biproduct universal property. Neither restrictPush
nor an extension/direct-image map is inverted. This directly repairs the
missing E-to-Omega relation rather than retaining the returned equations.

H12: I reread the rewritten `def-sfb-root-boundary-scalar-comparison` statement
against these declarations. It introduces E, Omega, M, N, e and every P,
fixes N_Omega and uniquely specifies e_Omega by its actual tensor-unit
adjunction equation (with existence and uniqueness), defines J,H,D and the actual target maps,
defines both full-source cospan arrows and the common boundary arrow, and
states exactly their biproduct equation. The node also includes the unique
model identity and uniquely
unit-normalized scalar extension of e, whose construction uses finite freeness. Its dependencies cite the existing scalar-functions and
condensation nodes; no copy of those scalar maps is introduced. Its Lean
record lists every delivered helper and its exact definition signature.
This is repair of a new definition node, not correction of the item's
unchanged mathematical statement.

H11: the former section was empty. The preceding checks and the following
clause and edge-case rereading replace it with an actual reading.

For the unchanged item I checked p and ell are prime and distinct, k has
characteristic p, E is a finite-dimensional normed Q_ell-algebra field,
Omega is its normed algebraic closure without completeness, and y is
separated, quasi-compact and locally of finite type with regular Y. The
chart is etale, and hproduct/hbranches specify exactly its SNC branches.
The actual pro-etale algebra a remains weakly etale under the upstream
small-site convention. `Assertion` quantifies over finite-dimensional M,
the supplied lisse N and its supplied e; it asserts `NormalizedComparison`
for all profinite P and all three naturality definitions. Reading
`NormalizedComparison` confirms it gives an isomorphism alpha, invertible
actual openUnit and beta, and lambda alpha beta = fullRestriction.
`boundaryModelDerivedMap` uses that same e. Module naturality uses maps
respecting e; parameter naturality is contravariant; `FamilyNaturality`
uses actual arrows of whole test schemes and their full module map. Thus
a family is not reduced to its individual Q-points. There is no invariant
or total nerve conclusion. The source's degree-zero and one-point
normalizations are the same defining equation with actual evaluation.

For the other new nodes, `zeroRoots` is the quotient evaluation setting
all roots to zero with named well-definedness and square theorems;
`test_boundary_square` supplies the actual exchange square. The
profinite-evaluation module specializes the library's canonical derived
comparison. Its ordinary helpers use the actual diagonal, generator, tensor-Hom
evaluation and adjunct; the retained evaluation-coherence theorem has a complete
proof in its docstring and the matching node clause. Its condensation is chosen from a full
sectionwise characterization, never from undetermined bare existence.
The present model identity relates that retained model to the library's
existing continuous-model presentation, including their module topologies.

I rechecked r=0 (empty root family, t-product 1, identity puncture), P empty
(zero free parameter and zero diagrams), P one point (ordinary module
unit and normalized one-point comparison), finite P (finite products),
M=0 (empty finite-free sum and zero tensor map), empty stratum (zero
site modules), and incomplete Omega (the module topology on each finite
product, with no completion or finite-subextension condition). In the
scalar equation the P-empty and rank-zero cases are zero maps on both
biproduct summands; the one-point case contains the actual tensor unit
on the model. Universes remain the shared u with Ab.{u+1}, and no site
object/morphism-universe equality is introduced. Every new variable is
explicitly bound with autoImplicit disabled.

The only additional postponed theorems are the uniquely characterized
model identity and uniquely
unit-normalized scalar extension of e (constructed using the finite-free ordinary model comparison). Their complete natural-language
proofs are in their docstrings. The model-presentation choice determines a
unique isomorphism; the scalar-extended supplied boundary datum is fixed
by its unit equation and existence-and-uniqueness theorem. All other
definition data are actual maps and adjuncts. No axiom, data-sorry, arbitrary
Omega-trivialization or new geometric hypothesis was added.

The scalar-unit criterion embeds the actual ordinary extension/restriction
adjunction equation in degree zero, retaining the whole arrow and the canonical
exact comparisons. Full faithfulness identifies it with the ordinary unit
criterion. The target-side derived maps use the same exact restriction transport.
The three new helper nodes use normed-field parameters F directly, as the item
does for E and Omega. This removes unused topological-ring generality from the
new helper definitions and adds no hypothesis to the unchanged item. The exact
restriction, ordinary extension and derived pushpull are reducible aliases of
their recorded constructions; the degree-zero functors are those same recorded
single-complex embeddings. The scalar maps reuse the existing coefficient inclusion.

All four delivered modules compile successfully with the prescribed scompile.py
wrapper, both individually and under their library module names. There are no
errors or unexpected warnings. The scalar module completes in 28.4 seconds as
a library module; the main theorem completes in 3.9 seconds. No heartbeat or
compiler-limit option is set in the delivered sources.
