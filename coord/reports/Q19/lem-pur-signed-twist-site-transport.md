## Worker report

Item: lem-pur-signed-twist-site-transport. The module
`Sheaf.Paper.SignedTwistSiteTransport` states
`WeilConjectures.PurityFiniteSetting.signedTwistSiteTransport`. Its only postponed
proof is this named theorem. All seventeen helpers are actual abbreviations,
section constructions or explicit predicates, with source and blueprint docstrings.
There are no new independent notions or dependency replacement modules.

The statement matches the source as follows.

* The datum k, ell, E, A and positive coefficient level is the existing
  `PurityFiniteSetting P`. The variable `n` is the predecessor of that positive
  level; `hlevel : P.level = n + 1` identifies it. Every source level is covered
  because P.level_pos says P.level >= 1. `signedSiteCoefficient` is literally the
  published `finiteTateCoefficient ell E n`, namely ULift of O_E/(varpi^(n+1)).
  `hA` spells out the source-implied annihilation ell^(n+1) A = 0, needed by the
  recorded root-line construction. It is no new arithmetic restriction: the
  positive ramification index implies ell in (varpi), hence ell^(n+1) in
  (varpi^(n+1)). No divisibility of the coefficient level by the ramification
  index is assumed.
* An arbitrary k-scheme is `(X : Scheme.{u}) (a : X ⟶ Spec (.of P.field.k))`.
  This explicit structure map is needed to use the recorded
  `diagonalExponent_isUnit`. There is no finite-type, smoothness, affine,
  separatedness, Noetherian, nonempty or dimension assumption.
* L_X(r) is `signedSiteEtale`: the existing `finiteEtaleTateSheaf`, at exponent
  ell^(n+1), with nonnegative tensor powers and actual internal-Hom duals.
  It is not an arbitrary line or a new root sheaf. The Z/m module action and
  balanced scalar extension are those in `finiteEtaleTateLine`.
* A_X(r) is `signedSiteModule`: the existing `finiteCoefficientTwist`, whose
  first line is the inverse-root-limit construction, with its specified powers
  and slice internal Hom. `signedSitePro` applies the recorded
  `finiteTateConstantRestriction` so it can be compared to fixed-ring module
  sheaves. This functor retains the original underlying sections and maps;
  it does not define another Tate twist. The signed formulas apply to the
  actual intrinsic dual object, not an abstract inverse line.
* nu_X is `ProEtale.comparisonUpperStar`. The nonnegative comparisons are the
  argument `b`, fixed by `hb : IsFiniteTateSiteComparison ...`. That recorded
  predicate gives the root-projection formula on every local pure tensor,
  including arbitrary pro-etale tests over etale objects and degree zero.
  Thus degree zero is the coefficient-unit map, degree one is the fixed
  root comparison followed by theta inverse, and higher degrees are its
  specified tensor powers, rather than arbitrary isomorphisms.
* The projection-induced theta_X is the argument `θ`, with
  `SignedSiteThetaNormalized`: every root-limit tensor is taken to its
  n-th projection tensor with the same coefficient. This is exactly the
  source's characterization of theta_X. The first line and finite tensor
  target are existing constructions, not unspecified data from existence.
* The result `∃! q` is the extension, with the first conjunct retaining b
  verbatim at every nonnegative exponent. `SignedSiteEvaluation` is the
  displayed evaluation equation for all negative degrees `.negSucc d` and
  their corresponding positive degrees `.ofNat (d+1)`. `signedSiteImage`
  uses the comparison-adjunction unit and restriction along every
  `f : W ⟶ toProEt(U)`. The etale evaluation is the existing `ihom.ev`;
  the pro-etale evaluation is the actual slice-Hom functional evaluated
  at the identity slice object. Its right side uses q_0 for the
  coefficient-unit comparison. Hence the equation incorporates the
  precise tensor and coefficient-unit transports in the source.
* The ordered pro-etale multiplication is `μ`, constrained by the published
  `SignedLineProductNormalized`: on every local basis it sends e_r tensor
  e_s to e_(r+s). This is the source's specified concatenation/contraction
  map, including mixed signs. The etale multiplication is `.p` of the
  published `finiteEtaleTwistPullbackData`. `SignedSiteMultiplication`
  states the multiplication square on all pulled local pure tensors, with
  arbitrary r,s in Z, arbitrary local sections, and all restrictions f.
  Pure tensors locally generate the sheafified tensor product. The comma
  category defining inverse image is filtered (the sites have finite
  limits), so pairs of pulled sections have common refinements. These
  local equations are the full morphism equality in the displayed square,
  not merely its action on global sections or one selected basis.
* The existential `τ` is the root-induced geometric pro-etale pullback
  family. The first clause of `SignedSiteGeometricLaws` is the existing
  `IsFiniteTateProPullback` in every nonnegative degree, fixing the maps
  by all root projections and retaining their scalars. Its second clause
  is the evaluation-transpose normalization in every negative degree,
  using the canonical inverse-image adjunction on every pro-etale test.
  Invertibility is part of each τ component's Iso type. Thus this is the
  specified geometric map, not an unconstrained comparison chosen to make
  the square commute. No inverse image is commuted with an infinite limit.
* `SignedSitePullbackSquare` states exactly the negative square for every
  scheme map v, using the fixed etale `.c` map (already root and dual
  evaluation normalized), the actual canonical
  `comparisonUpperStarCompUpperStarIso`, and q on X and X'. The structure
  map on X' is v followed by a, as appropriate for k-scheme morphisms.
* Identity and composition are the third and fourth conjuncts of
  `SignedSiteGeometricLaws`, for every signed exponent. They use the
  canonical `ProEtale.upperStarId` and `ProEtale.upperStarComp`, including
  the action of the outer pullback functor. The evaluation clause gives
  the requested dual-evaluation coherence. The canonical comparison mate
  and etale comparisons have the recorded identity and composition laws,
  so these are also the identity/composition compatibilities of the squares.
* `SignedSiteRootCoefficient` is the final degree-one coefficient-map
  identity. The left side is q_1 on z tensor 1_A, pulled by the actual
  adjunction unit and arbitrary restriction. The right side is theta^-1
  of c(z) tensor 1_A, with c exactly `ProEtale.cartierRootsIso`. The latter
  is the same-root comparison in the dependency. Thus it is precisely
  sigma_X c_m,X, as a coefficient-sheaf morphism before cohomology.

Dependency declarations inspected and reused:

* `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`
  and its actual coefficient quotient and finite-field datum.
* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, with its
  locally affine locally ringed-space definition, and scheme morphisms.
* `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`:
  `Scheme.etaleFiniteTwistPullback`, `FiniteEtaleTwistPullbackData`, and
  `finiteEtaleTwistPullbackData.c` / `.p`, with every recorded normalization.
  Its imported `FiniteEtaleTateSheaf` owns the integer root-line construction.
* `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: reexports
  `finiteCoefficientTwist` and `coefficientTwistLine` from
  `CoefficientTwistsDetailed`, retaining the root-limit finite reduction.
* `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparison`, the inclusion and Kan-extension
  adjunction; its fixed-module presentation is `comparisonUpperStar`.
* `Sheaf.AlgebraicGeometry.FiniteRootSiteComparison`:
  `Scheme.finiteRootSiteComparison`, `FiniteRootSiteComparisonSpec`,
  `finiteRootProTensor`, `finiteRootProGenerator`, and the recorded
  same-root `ProEtale.cartierRootsIso`.
* `Sheaf.Paper.PurityFrameClass`: `PurityFiniteSetting.frameClass`, its
  imported fixed-root coefficient setting and frame construction. Its
  published interface uses the comparison-pullback root-line presentation;
  this item exposes the source's projection characterization explicitly
  as `SignedSiteThetaNormalized`, without changing that dependency.
* `Sheaf.Paper.FiniteTateSiteDescent`: `Scheme.finite_tate_site_descent`,
  `finiteTateCoefficient`, `finiteTateConstantRestriction`,
  `IsFiniteTateSiteComparison`, `IsFiniteTateProPullback`, and the pure
  local tensor generators. Their full signatures and docstrings were read.
* `Sheaf.Algebra.Homology.SignedLineDerivedBaseChange`:
  `SheafOfModules.SignedLineDerivedBaseChange.signed_line_derived_base_change`,
  including its evaluation normalization and uniqueness clauses.
* `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`:
  `ProEtale.supportSiteComparison_pullback_coherent` and the underlying
  canonical comparison maps; the square uses the existing unprefixed mate.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, the existing sheafified tensor;
  no new monoidal structure is installed.
* `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObj`, U ↦ Hom over the localized ringed site.
* Added landed definition dependency
  `def-sf-signed-line-product-normalization-data`, module
  `Sheaf.Paper.SignedLineScalarTensorTower`: its recorded existing declarations
  `SheafOfModules.SignedLineProductNormalized` and
  `SheafOfModules.SignedLineBasisPowers` give exactly the ordered mixed-sign
  multiplication normalization predicates. This definition node owns the
  predicates; no existence theorem or chosen object is used. Their independent
  object and morphism universes are explicitly instantiated. The item's
  mathematical statement and proof are unchanged.

Every recorded proof-dependency module is imported, as a plain import where
it is needed only by the future proof. This includes root-projection reduction,
relative tensor comparison, finite-free dual pullback, exact comparison,
tensor closedness and the independent inverse-image tensor comparison.

Edge cases checked: n=0 represents source level one; the empty scheme is
allowed; ell=2 is allowed (there is no Koszul sign in these ordinary sheaf
powers); ramified E and coefficient levels not divisible by e are allowed;
all positive and negative powers use actual tensor/dual constructions.
For multiplication checked (0,r), (r,0), (2,-1), (1,-2), (-1,-1), (1,-1)
and reversed orders. Opposite equal exponents evaluate to the unit, not an
unspecified endomorphism. All scheme maps, identities and composites are
quantified without any smoothness or finite-type restriction. The small
pro-etale object universe remains u+1 and its morphism universe remains u.
No source correction or STATEMENT-DISPUTED fault was needed.

Searches performed:

* msearch.py leanfinder: "Finite etale proetale Tate twist comparison extends
  to negative dual powers preserving multiplication evaluation and scheme
  pullback". Eight hits, including BDeRhamPlus, BDeRham, Fontaine theta
  maps and etale ring scalar-extension results; no match for this statement.
* msearch.py loogle: "CategoryTheory.Sheaf, CategoryTheory.MonoidalCategory".
  Nine hits: general sheaf monoidal/symmetric structures, sheafification and
  point-fibre monoidal instances; none states the signed normalized comparison.
* msearch.py grep: "TateTwist|tateTwist|signed.*[Tt]wist|[Tt]wist.*[Ss]ite".
  Zero Mathlib hits.
* rg in lean/WeilConjectures and lean/Sheaf for signed site comparisons,
  SignedTwist and the item's id: found generic signed-line base change,
  scalar tower, integral comparisons, existing positive Tate descent and
  supported-cup presentation; none gives this actual signed comparison
  between the specified etale and intrinsic pro-etale twists. Exact-name
  searches for the new signedSite declarations found no existing declaration.
* Read the local Stacks source at sites-cohomology.tex
  lemma-pullback-tensor-product (07A4), and sites-modules.tex
  remark-pullback-internal-hom (0GMX) and example-dual (0FNY).

Validation uses only scompile.py and deliver2.py. The initial type probes were
removed. A first normalization-predicate elaboration needed explicit
`.{u+1,u,u+1}` universes and its existing coefficient ring sheaf, which was
repaired without equating site universes. Final compile and preflight results
are recorded below after their completion.

## Second reading by Q19

I reread the node and the generated module in a separate checking pass. This
is a self-check by the dispatched worker; no other agent was started, as the
launcher explicitly forbids it. The maintainer's independent review remains
the independent second reader.

The pass checked the local-section equations against the actual underlying
objects: positive etale powers and intrinsic pro-etale powers are not silently
identified; they are linked by q. Negative pro-etale sections are actual slice
Hom maps. The order in etale ihom.ev is positive then dual, giving the source's
dual-first evaluation after symmetry, with no sign. The multiplication tests
use arbitrary pure sections and arbitrary refinements rather than chosen
bases alone. The fixed nonnegative comparisons are retained verbatim, and
theta's projection formula, the same-root c and scalar 1_A appear explicitly
in the final coefficient identity. The pullback square has k_v in the required
orientation and includes the canonical identity and composition maps. The
pass found two interface issues: universe inference for the existing
SignedLineProductNormalized predicate needed explicit site and coefficient
universes; and the ordered multiplication family must be indexed by k-schemes
with their structure maps, as in the node, rather than by all schemes. Both
were corrected. In particular no multiplication on characteristic-ell schemes
is required by a hypothesis. No clause was dropped or weakened, and no
statement correction was made.

Server compile: PASS, no warnings, sandbox 57.3 s and library module 42.5 s.

## Returned-delivery repair (2026-10-23)

Repaired the sole H2 point returned on immutable head `ecc9bea628a4`:
`stmt_deps` now cites the landed, reviewed definition owner
`def-sf-signed-line-product-normalization-data` in place of
`lem-pur-signed-line-scalar-tensor-tower`. The latter was used only for the
plain normalization predicate, not a theorem-produced object. Read the
owner's full statement, existing Lean record, and the two predicate definitions
in `Sheaf.Paper.SignedLineScalarTensorTower`; the owner supplies exactly the
predicates used here. Updated `lean.note` and the dependency account above.
The original mathematical statement, proof, proof dependencies, and Lean module
are unchanged. No new nodes or replacement dependency modules are needed.

Compared the retained packet with the current read-only base: only `lean` and
this added definition dependency differ in the item node. The module SHA256
before and after repair is
`a87151bfc3d48c4110f1946601f3fd68a56e63cb01842f45fb4ce009e14e817d`.
The saved packet's initial dry run passed at `f2256b29df1`; the independent
review's dependency-ownership correction was nevertheless required and has
been applied. The self-check confirms that `hμ` uses the plain predicate and
no `.choose` or constructed object, so the definition node is the appropriate
statement dependency. The earlier independent review accepted all other
hypotheses, clauses, edge cases, universes and docstrings.

Repair validation: scompile.py PASS on 2026-10-23, both sandbox and library
module, with no errors or warnings. Rechecked the verbatim theorem signature,
the unchanged module hash, and the corrected definition ownership.
