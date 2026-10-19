## Worker report

The delivery states `WeilConjectures.zlFiniteAdicDirectImage` in
`Sheaf.Paper.ZlFiniteAdicDirectImage`. Its sole postponed theorem has proof `sorry` and
an eleven-step proof docstring following the node's reviewed proof. All other declarations
are real constructions or structures packaging clauses of this same theorem. No natural
statement, dependency list, proof, or other node field is changed. No dependency is restated.

The former worker's stale-assignment diagnosis was incorrect for stage 2. Q88's reviewed
split completed stage 1; the current node has no `lean` or `reviewed_lean` record. This
assignment supplies its first Lean statement, without splitting the DAG again.

The simultaneous system is needed to state naturality between different finite-morphism
diagrams and different coefficient fields. It is an existence assertion about the actual
specified categories and operations. It does not assume an arbitrary pushforward, stalk
map, equivalence, coefficient category, or Frobenius operator. The integral functor has exactly the recorded completed-derived-image objects;
`integralComparison_normalized` makes its comparison the equality transport on those
objects. The rational functor has exactly the localized integral objects, with the
same identity normalization in `rationalComparison_normalized`. The integral counit
is constrained by `integralCounit_reduction`, using the canonical scalar-extension
unit, the recorded resolution-normalized restriction comparison, and the canonical
finite derived counit. `counit_localization` fixes the rational adjunction counit to
that integral map, through the prescribed pullback/localization comparison. All
displayed stalk/exchange maps use this normalized counit and the dependency's canonical
composition comparisons. Fixing only the right-adjoint functor was insufficient in
the returned version; that H3 defect is repaired here. The auxiliary structures are packages of this node's
own clauses, not additional independent mathematical notions or assumptions.

Hypotheses and clauses, in the order of the natural statement:

| Natural statement | Lean rendering |
| --- | --- |
| Global finite-field datum p,a,q,k0,k | `D : FiniteFieldDatum.{u}`; the dependency carries primality, a≥1, q=p^a, cardinality, and the fixed algebraic closure with its structure homomorphism. |
| Prime l distinct from p | `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)`. |
| Finite extension E/Q_l | The `rational` field quantifies `(A : Type u) [Field A] [Algebra (Padic l) A] [FiniteDimensional (Padic l) A]`. No unramifiedness or split-coefficient condition is imposed. This also gives the rational clause for every finite field embedded in Ω; its embedding is used explicitly in the common-stage construction. |
| Algebraic closure containing the finite coefficient stages | `(Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]`; `AlgebraicallyClosedCoefficients.Index l Ω` is the actual finite-subfield poset. `Coefficient.{u}` and its Shrink algebra equivalence are the dependency's small coefficient model. |
| Lambda=E or Qbar | `sfRationalConstructibleCategory` at each finite field and the actual `generalAlgebraicallyClosedConstructibleCategory` pair category via `StageSystem.Morphism.functor`. |
| X,Y separated finite-type k-schemes | `ZlFiniteAdicSpace D` only bundles `Over (Spec (.of D.k))`, `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` of its structure morphism. Its four projection instances recover those exact standard hypotheses. Every such scheme supplies this bundle directly. |
| f finite | Each system's `image`, `fibre`, `stages`, and final clauses quantify the actual scheme map with `[IsFinite f]`. There is no étaleness, reducedness, smoothness, or surjectivity assumption. |
| Derived direct image from the dependency | `integral_obj` fixes the ambient objects to `sfCompletedDerivedDirectImage`; `integralComparison_normalized` fixes the maps of the comparison to equality transport. `rational_obj` and `rationalComparison_normalized` do the same for scalar localization. `integralCounit_reduction` and `counit_localization` tie the adjunction to the recorded scalar unit and normalized finite counits. The proof docstring specifies these equations, in addition to the right-adjoint universal property. |
| Rf_* maps D^b_c(X) to D^b_c(Y) | The source and target of `image.functor` are precisely the recorded rational constructible categories; the common-stage `stages.functor` has their actual pair categories as endpoints. Thus constructibility and boundedness are included in the functor's type. |
| t-exact for the standard constructible structures | `image.exactness.tExact` uses `sfRationalStandardTStructure`; `commonExactness.tExact` uses `sfCommonStageStandardTStructure`. Both halves and every integer degree are retained. |
| Exact heart restriction f_*^c | `exactness.heart`, `heart_fac`, `heart_limits`, and `heart_colimits` in the imported `ConstructiblePullbackComparison` give the restriction to the recorded full hearts and preservation of finite limits and colimits. `commonExactness` gives the same at Ω. No chosen substitute abelian category occurs. |
| Natural H^j(Rf_*K) ≅ f_*^c H^j(K), all K and j∈Z | `exactness.cohomology : ∀ j : ℤ, ...` is the natural isomorphism between actual truncation-cohomology functors and direct image. `cohomology_formula` fixes its components as the normalized truncation and shift comparisons; `truncLE_counit` and `truncGE_unit` fix the truncation maps. Its values lie in the recorded full heart. The common-stage field has the same clauses. |
| Any geometric ybar:Spec k→Y | Every `fibre` and common-stage restriction clause quantifies `y : Spec (.of D.k) ⟶ Y.space.left`. It is not restricted to a k-linear map, a selected closed point, or a rational model point. |
| S=X×_Y Spec k | `zlFiniteAdicFibre D f y` has underlying chosen `pullback f y` and structure map `pullback.snd f y`; the map to X is `pullback.fst f y`. Its geometric properties are inherited by finite base change. |
| F a constructible sheaf; F_S inverse image | The finite-field invertibility clauses quantify `K : sfRationalHeart ...`. The argument to the fibre image is `(zlFiniteAdicPull ... (pullback.fst f y)).obj K.obj`, the recorded derived inverse image, whose heart interpretation is the imported constructible-pullback t-exactness statement. The Ω clauses quantify the actual `sfCommonStageHeart`. |
| Finite set P_y of geometric lifts | `ZlFiniteAdicLifts D f y` is exactly `{x : Spec k ⟶ X // x ≫ f = y}`. `fibre.finite` asserts its finiteness without choosing an ordering. |
| First canonical isomorphism: image stalk→H0(S,F_S) | `zlFiniteAdicExchange` is the adjoint of pullback of the counit across the actual pullback square. `fibre.baseChange` makes H0 of its point-fibre image invertible. `ordinary.property` normalizes comparison with the very Roos vertex used by `integralImage`; `zlFiniteAdicOrdinaryProjection` exposes that dependency's existing chosen projection. `zlFiniteAdicOrdinaryComparison` localizes it. `zlFiniteAdicFibreRestriction` composes exchange with this comparison before point H0, so its target is actual `rationalOrdinaryCohomology ... 0`. The former unnormalized object equality has been replaced by this canonical comparison. |
| Second canonical isomorphism: H0(S,F_S)→direct sum of stalks | `zlFiniteAdicEvaluation` constructs each germ component. `zlFiniteAdicModuleSumMap` uses the finite direct-sum/product equivalence to construct the unique linear map with those components, and `zlFiniteAdicStalkToSum` applies it to all geometric lifts. `fibre.stalkToSum` asserts invertibility. `zlFiniteAdicFibreToSum` composes inverse normalized ordinary comparison, inverse exchange and the fixed stalk-to-sum map. Its source is actual ordinary H0. The adjunction triangle identities identify its components with restriction on S. This spells out both isomorphisms rather than replacing the middle object by a sum. |
| Lambda-linear maps | Point H0 takes values in `ModuleCat.{u} E`, all its maps are module morphisms, and the sum map is `ModuleCat.ofHom` of an actual linear map. At Ω the target is `ModuleCat.{max u v} Ω` and all maps are actual extension-of-scalars module morphisms. |
| Natural in sheaf morphisms | `exchangeNatural` is the exchange naturality square, and `evaluationNatural` is each germ square. The finite-sum map is uniquely fixed by these components, so these equations give naturality of both displayed isomorphisms, including their inverses. |
| Natural in diagram isomorphisms, including semilinear ones | `diagramNatural` quantifies isomorphisms a:X'≅X, b:Y'≅Y and σ:Spec k≅Spec k, the commuting square, transported geometric points, and both point-return equations. It equates the two routes through the explicitly constructed exchange and evaluation maps. `zlFiniteAdicPointTransport` uses exactly the dependency's composition comparisons. There is no `IsOver (Spec k)` requirement on a,b,σ or f. Thus automorphisms of k acting semilinearly are included. Every component goes to the component at the transported lift with its induced stalk transport; the finite-sum universal property gives the claimed reindexing of the whole sum and the corresponding finite-fibre section comparison. |
| Qbar functors and all maps come from common finite stages | `stages` is an actual `StageSystem.Morphism`, including its associator coherence and map on every common-stage representative. `stageFunctor` identifies each finite functor with its rational `image.functor`. `stageMate` identifies its β with `zlFiniteAdicScalarExchange`, the explicit adjunction mate of the recorded `rationalPullbackScalarComparison`, after the dependency's stage-transition identifications. This includes identity and repeated coefficient stages. It fixes the actual comparisons and descends counits, exchange, evaluation, cohomology and diagram naturality. `zlFiniteAdicQbarFibreMap` and `zlFiniteAdicQbarStalkToSum` literally extend the finite-stage restrictions to Ω (the latter component by component); `commonBaseChange` and `commonStalkToSum` assert invertibility for every common-stage heart object. The common-stage fibre map now literally composes with `zlFiniteAdicOrdinaryComparison` at that stage, so its middle module is the recorded `adicOrdinaryCohomology`. No equality of u and v is assumed. |

Dependencies read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum` and the coefficient conventions.
- `Sheaf.Paper.SfConstructibleHeart`: `sfRationalHeart`, `sfCommonStageHeart`, their
  predicates and their prescribed standard t-structures.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
  The morphism-properties dependency is a convention record and explicitly has no
  declaration of its own; its named Mathlib scheme-over-base, finite-type, quasi-compact
  and separated structures are used directly.
- `Sheaf.Paper.SfDerivedDirectImage`: `sfCompletedDerivedDirectImage` and its actual
  completed module construction; the proof uses its `SfIntegralDirectImage` reduction tower.
- `Sheaf.Paper.LocalFrobeniusTrace`: `localPullbackComposition` and the same derived
  geometric-stalk/point-fibre convention, without imposing a Weil structure on the sheaf.
- `Sheaf.Paper.PbcQbarStandardCohomology`: read together with its public import of
  `PbcCohomologySheaves`. Its generic Mathlib `DerivedCategory.homologyFunctor` match and
  the actual standard truncation-cohomology construction are used; there is no second
  cohomology-sheaf definition. Its PBC-specific Qbar category is not substituted for the
  intrinsic coefficient category in this item.
- `Sheaf.Paper.CommonStageCompactWeilCohomology`, through `OrdinaryCompactCohomology`:
  `rationalImage`, `rationalOrdinaryCohomology`, `adicOrdinaryCohomology`, and
  `pointRationalFibre`/`coefficientFdCohomology` for the actual middle coefficient module.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: its declaration and docstring
  were obtained with `scompile.py --source`, since this recorded module is absent from the
  older local source checkout. As its docstring specifies, geometric base change here is
  Mathlib's `pullback`, with its two projections, rather than its module-pullback helper.
- `Mathlib.FieldTheory.IsAlgClosed.Basic` and `Scheme.SpecToEquivOfField`: the recorded
  unbundled geometric point is the actual map `Spec (.of D.k) ⟶ X`, not a new point type.
- `Sheaf.Paper.ConstructiblePullbackTExact`: reuse `ConstructiblePullbackComparison` as a
  general clause package, `constructiblePullbackResidueUnits` to discharge the dependency's
  invertibility structures, and the actual pullback/point-fibre t-exactness statement.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`, `DerivedPullbackTensorHom` and
  `WeilConjectures.CategoryTheory.StageSystem.Functor`: the recorded stages, small
  coefficient fields and inclusions, rational scalar and pullback comparisons, and the
  actual coherent pair-category descent functor. All available recorded proof-dependency
  modules are imported without `public`; statement-dependency modules are public.

Edge cases checked before finalizing:

- Empty schemes, an empty geometric fibre and an empty lift set: no nonempty hypothesis
  occurs; the constructed finite direct sum is zero and its map is still defined.
- Identity map and one-point fibre: equality-normalized functor comparisons, the finite
  tensor-unit counit, and `counit_localization` give the positive canonical germ map.
  Replacing the counit by its negative while retaining those comparisons violates the
  localization equation on a characteristic-zero one-dimensional coefficient object.
  Negating either comparison is also excluded by its equality-normalization field.
- Two disconnected points: both components occur independently, with no ordering or
  choice of a distinguished point. Diagram isomorphisms may exchange them.
- A finite nonreduced fibre, e.g. Spec(k[ε]/ε²): the theorem requires finiteness, not
  finite étaleness or reducedness, and counts geometric lifts rather than algebra length.
- All integer cohomological degrees, including negative degrees; torsion integral
  representatives and their negative derived Tor terms are retained in the proof.
- Ramified finite coefficient extensions and repeated or identity stages: no exclusion;
  β is the actual scalar mate at every inclusion and the stage system includes coherence.
- Arbitrary semilinear base automorphisms, including the identity: no linearity restriction
  on diagram or point isomorphisms. No Weil structure, weight, lissity or semisimplicity
  assumption has entered the assertion.
- Independent closure universe v: scalar extension explicitly uses `max u v`; no site
  object/morphism universe or coefficient universe is collapsed.

Searches for an existing full statement (2026-10-18):

- `msearch.py leanfinder`, query “Derived direct image for a finite morphism is t-exact
  on rational constructible adic complexes and stalks are sums over finite fibres”:
  eight hits, including `Condensed.profiniteSolid`, finite affine algebra facts,
  `Functor.instLinearDerivedCategoryMapDerivedCategory` and the abstract exact-derived
  functor comparisons. None is this adic constructible finite-image theorem.
- `msearch.py loogle`, query
  `AlgebraicGeometry.Etale.lowerStarSheafFiberIsoPi, CategoryTheory.Functor.IsTExact`:
  zero hits, unknown identifier for the project-specific étale stalk declaration.
- `msearch.py leansearch`, query “finite morphism derived direct image exact rational
  adic sheaves finite geometric stalk sum”: eight hits, principally `IsFinite`, its
  constructor/recursor, and algebraic `AdicCompletion.sum`/`sumInv`. No statement match.
- `msearch.py grep`, expression `finite.*(adic|stalk)|IsTExact` in `AlgebraicGeometry`:
  ten structure-sheaf stalk / quasi-finite scheme hits, none about adic direct image.
- Direct `rg` searches in upstream `WeilConjectures/` and project `lean/Sheaf` for finite
  rational/adic images, `finiteLowerStar`, `lowerStarSheafFiberIsoPi`, finite t-exactness,
  and the exact item id. Upstream `SixFunctors/Finite/Stalk` is the finite-level étale
  result, and `SixFunctors/ProEtale/Adic/LowerStar` concerns a different adic category;
  neither supplies this rational/common-stage statement with its middle H0 and naturality.
  The current SF integral-image, ordinary-cohomology, pullback and heart interfaces were
  reused. Exact-id and new-name searches in `dag/lean_names_upstream.json`, upstream
  sources and project sources found no existing declaration of this item or name collision.

No `STATEMENT-DISPUTED` flag, statement correction, new independent node, or unusable
recorded statement dependency was found. Missing canonical assembly belongs to this
node's direct-image/restriction assertion and is supplied by its explicitly defined maps
and clause packages, rather than by an arbitrary comparison hypothesis.

Validation: all compilation is through the prescribed `scompile.py`, file by file with
its unchanged 60-second limit. The draft compiled cleanly, with its single expected
sorry. Final import-complete compilation and the dry-run delivery check are recorded below.

Validation of the returned packet before this repair: import-complete `scompile.py` passed without errors or warnings
(20.8 seconds for the sandbox check and 49.7 seconds for its library-module check).
`deliver2.py --no-push` printed OK: the packet compiles and passes the server preflight.
Only the three intended delivery paths were staged. The final module documentation
lists its main constructions and statement explicitly.


## Repair of return c7712dc28585

H3 was substantive. An adjunction with the same left and right functors can have its
counit negated and its unit negated. Naturality, triangle identities and invertibility
of the resulting fibre maps would still hold. The old `integralComparison` and
`rationalComparison` fields imposed no compatibility with the counit, and could also
absorb a sign. The repaired image package therefore adds four levels of normalization:

1. `integral_obj` and `integralComparison_normalized` restrict the ambient functor
   comparison to equality transport to the actual `sfCompletedDerivedDirectImage`.
2. `rational_obj` and `rationalComparison_normalized` fix localization in the same way.
3. `zlFiniteAdicImageReduction` is the scalar-extension transpose of direct image of
   the canonical quotient unit and `sfDerivedRestrictionComparison`. The equation
   `integralCounit_reduction` makes reduction of the integral counit equal the recorded
   pullback reduction, pullback of that image reduction, and `zlFiniteAdicFiniteCounit`.
   This last map comes from `proEtaleConstantRingAdjunction`, normalized by the tensor
   unit, transported through `proEtaleUnitLerayDirectImageIso` (identity on sections),
   then the standard derived adjunction. All n>=0 are quantified (exponent n+1),
   and every good representative and its comparison are quantified.
4. `counit_localization` says that the rational adjunction counit is precisely this
   integral counit localized, conjugated by the fixed rational and pullback comparisons.

The old `ordinary` equality could not carry the required normalization between the
ambient right-derived presentation and the dependency's selected Roos vertex. It is
replaced by the `ZlFiniteAdicOrdinaryData` subtype, whose comparison is
constrained by its projection equation against
`zlFiniteAdicOrdinaryProjection`. That helper opens the exact witness already selected
in `integralImage`, using the same theorem and choices; it constructs no replacement
cohomology. `zlFiniteAdicOrdinaryComparison`, `zlFiniteAdicFibreRestriction` and
`zlFiniteAdicFibreToSum` now give both actual H0 arrows explicitly. The Qbar fibre map
also composes the finite-stage normalized ordinary comparison before scalar extension.
These are representation choices and compatibility clauses for the node's canonical
restriction maps, not a change to its mathematical statement.

Additional source/API inspection for this repair: read the node and every current
statement-dependency record, the finite-image proposition in
`literature/stacks-project/etale-cohomology.tex` at lines 8245--8290, the full signatures
and normalization docstrings of `sfDerivedRestrictionComparison`,
`integralPullbackReductionIso`, `localPullbackObjectIso`,
`proEtaleConstantRingAdjunction`, `proEtaleUnitLerayDirectImageIso`,
`Adjunction.mapDerivedCategoryRightDerivedAdjunction`, and the construction of
`integralImage`. The only extra import is
`Sheaf.AlgebraicGeometry.ProEtaleUnitLerayChainFormula`, reusing its existing
identity-on-sections comparison; no canonical operation is redeclared.
Direct searches for `proEtaleConstantModuleDirectImage`,
`proEtaleConstantRingPushforward.*≅` and `RingDirectImageMap.*CoefficientDirectImageMap`
located that existing comparison. The retained original searches above concern the
full theorem. Comparing parsed node records with the current shared node finds no
difference outside `lean`; the current base still has no statement for this node.
The initial prescribed saved-packet dry run printed OK at a214357df7; that was only
a baseline and is superseded by the repaired validation below.

## Second reading by NU

This is a separate self-check pass by the dispatcher worker, with the node and the
repaired module open; the instruction forbids starting another agent. Independent
review remains with the maintainer. The following is the actual second reading,
replacing the absent/non-substantive reading in the returned delivery (H11).

- **Geometric and coefficient hypotheses:** the node fixes p,a,q,k0,k and l!=p;
  `D`, `l`, `[Fact l.Prime]`, `hl` retain those. `ZlFiniteAdicSpace` has only the
  scheme over Spec(k) and finite type, quasi-compactness and separatedness of its
  structure map. `image` quantifies every finite scheme morphism, without an over-k
  condition. `rational` quantifies all finite extensions, including ramified ones;
  `Ω : Type v` with its specified algebraic closure is independent of u. No extra
  smoothness, étaleness, lissity or nonempty hypothesis was found.
- **The specified Rf_*:** I followed `image.integral` through `integral_obj` to the
  actual completed module right-derived functor, and through `rational_obj` to the
  recorded raw scalar localization. Naturality of the identity-normalized comparison
  fixes the integral and rational map actions. I tested the return's negation example:
  neither the two comparison maps nor the localized adjunction counit can be negated
  while keeping the new equations. The new `integralCounit_reduction` has reduction
  of the counit on its left and, on its right, first rho_f, then f* of the normalized
  direct-image reduction, then the actual finite counit; the direction and endpoints
  agree. This is the H3 repair, not merely a claim that adjunctions are canonical.
- **Boundedness, constructibility, t-exactness and exact heart:** the endpoints are
  `sfRationalConstructibleCategory`, not ambient derived categories. `exactness.tExact`
  uses the recorded standard t-structures on those exact categories. The reused
  `ConstructiblePullbackComparison.heart_fac` fixes restriction to the full hearts;
  `heart_limits` and `heart_colimits` supply exactness. `commonExactness` gives the
  identical clauses in the actual common-stage category. I found no substituted heart.
- **Every cohomological degree and naturality:** `exactness.cohomology` quantifies
  all j in Z and is a natural isomorphism of functors. Its formula is constrained by
  the two truncation equations and the shift comparison, so it is the standard
  H^j comparison, not an unrelated object isomorphism. Negative j are included.
- **The fibre, inverse image and finite set:** `zlFiniteAdicFibre` is the actual
  `pullback f y` with its second projection; `zlFiniteAdicPull (pullback.fst f y)`
  is the given inverse image. `ZlFiniteAdicLifts` retains every map Spec(k)->X
  satisfying x>>f=y; `fibre.finite` asserts finiteness without an ordering. The
  empty set and a finite nonreduced fibre are admitted.
- **The first restriction and the actual middle H0:** `zlFiniteAdicExchange` is
  the adjoint of pullback of the now-normalized counit. `fibre.baseChange` asserts
  its invertibility after point H0 on every heart object. I traced the middle object
  through `ordinary.property` to the exact Roos projection selected by
  `integralImage`. `zlFiniteAdicOrdinaryComparison` is its localization, and
  `zlFiniteAdicFibreRestriction` includes that comparison before point H0. Thus its
  target is the dependency's ordinary cohomology, rather than only some isomorphic
  coefficient module. This part changed during the H3 repair.
- **The second restriction and linearity:** `zlFiniteAdicEvaluation` uses the same
  normalized counit. `zlFiniteAdicModuleSumMap` constructs the linear map with those
  components, using finite direct sum/product comparison. `fibre.stalkToSum` asserts
  invertibility. `zlFiniteAdicFibreToSum` starts at actual ordinary H0, undoes the
  normalized comparison and exchange, and applies this sum map. Its components are
  consequently the restrictions on the fibre. ModuleCat morphisms give E-linearity;
  the scalar extension functor gives Ω-linearity. The empty sum is zero.
- **Sheaf and diagram naturality, including semilinear diagrams:** I read
  `exchangeNatural`, `evaluationNatural` and every binder of `diagramNatural`.
  The latter allows arbitrary a,b,σ isomorphisms subject exactly to the commuting
  square and point-return equations; it imposes no IsOver condition. `wx` matches
  each transported lift, and `zlFiniteAdicPointTransport` supplies its stalk map.
  The sum map's component construction therefore gives the asserted reindexing.
  The normalized ordinary comparison preserves those identities through its Roos
  projections. Identity diagrams and the exchange of two fibre points remain present.
- **Common finite stages:** `stages` is the recorded coherent `StageSystem.Morphism`;
  `stageFunctor` fixes its finite functors and `stageMate` fixes its beta by the actual
  scalar mate. The Qbar fibre map now extends the normalized finite H0 restriction;
  the sum map extends each normalized germ. `commonBaseChange`, `commonStalkToSum`
  and `commonExactness` retain the three assertions for all common-stage heart
  objects. Identity and repeated coefficient stages and the independent universe v
  are included; there is no arbitrary endomorphism or Frobenius datum.

The mismatches found in this pass were exactly the unnormalized comparison/counit
interface and its inadequate ordinary-object equality, repaired as above. No further
natural-statement mismatch or statement correction was found. There are no new DAG
nodes or dependency modules. The sole postponed theorem remains the node's own
`zlFiniteAdicDirectImage`, with its proof docstring updated at Steps 5 and 8.


Repair elaboration check: the first expanded record hit the default deterministic
heartbeat bound while generating `ZlFiniteAdicRationalSystem` constructor laws;
downstream missing-field errors were consequences. A temporary profiled prefix
located the cost in `Meta.mkNoConfusion`. The dependent ordinary comparison and its
projection equation were therefore factored into the `ZlFiniteAdicOrdinaryData`
subtype in the same module, reusing Subtype's constructor laws. The ordinary
comparison subtype itself needs no generated no-confusion theorem. The explicit
`zlFiniteAdicFibreFinite` projection instance carries the existing finite-base-change
instance through the chosen fibre bundle. Explicit finite-counit result type and bundle arguments, and reuse of
`zlFiniteAdicFibreRestriction` at Qbar, also reduce elaboration. No timeout or
heartbeat limit was increased, no module was split, and no profiler option remains
in the delivered file.

The remaining deterministic elaboration diagnostic was confined to the first H0
arrow, while the second H0 arrow elaborated. Its result type and the fibre pullback
bundles are now explicit, and its two point-H0 maps are composed in ModuleCat.
This is the same restriction composite by functoriality, without an expensive
inferred intermediate derived object. All checks still use the original limits.

A tiny wrapper-compiled options probe confirmed the supported generation options.
The final module disables unused generated constructor-injectivity and size-of
lemmas (`genInjectivity false`, `genSizeOf false`), following Mathlib's convention
for category-theoretic data packages. This changes no field, constructor or
mathematical clause and does not raise any resource limit.

Final repaired-source validation (2026-10-18): prescribed `scompile.py` exited 0,
with no errors or warnings, for both the sandbox check (59.6 s reported) and
`Sheaf/Paper/ZlFiniteAdicDirectImage.lean` (37.7 s). No resource limit was changed.
The item record still differs from current main only in `lean`, its signature is
verbatim, every owned declaration is listed, all Lean lines have at most 100
characters, and only the node's own theorem has `sorry`.
