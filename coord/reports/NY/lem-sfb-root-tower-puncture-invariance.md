## Worker report

The delivery states `AlgebraicGeometry.ProEtale.rootTower_puncture_invariance` in
`Sheaf.Paper.RootTowerPunctureInvariance`. Its only theorem has proof `sorry`.
The auxiliary definitions have actual data and expose the particular adjunction,
comparison, exchange, inverse and naturality conditions occurring in the statement.
No coefficient vanishing theorem is claimed proved.

This repairs the independent return at immutable head 47122defe385. The
projection is now written directly as `Spec.map (CommRingCat.ofHom (algebraMap R
(tameRootAlgebra p (fun i ↦ a (t i))))))`. The import of
`Sheaf.Paper.RootTowerLisseMorphismExtension` and the added theorem stmt_dep
`lem-sfb-root-tower-lisse-morphism-extension` are removed. The canonical map is
definitionally the old helper's body, so all hypotheses and conclusions are
preserved. The current live node still has `lean: null`; comparison with the
saved packet shows only `lean` and `stmt_deps` differed. The delivery wrapper
refreshes and rebuilds on current main. No source statement is corrected.

Hypothesis and clause correspondence:

- Distinct primes are `(p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)`.
  The characteristic-p field is `(k : Type u) [Field k] [CharP k p]`.
- The finite norm-topological extension is `(E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]`. The chosen algebraic closure
  with extended norm is `(Ω : Type u) [NormedField Ω] [NormedAlgebra E Ω]
  [IsAlgClosure E Ω]`. In particular Ω is not assumed complete. The two main
  conjuncts use E and Ω respectively; neither is replaced by a finite-coefficient
  or finite-subextension-valued ring.
- `Profinite.continuousCoefficientRingObj F` is the existing same-universe
  all-continuous-map coefficient construction. I read both it and the recorded
  `Profinite.continuousMapRingObjOfUniverse`: both have sections
  `ULift.{u+1} C(P,F)` and precomposition restrictions when the coefficient and
  profinite universes are u. Their monoid structure is the existing ring-sheaf
  sectionwise multiplication transported through the canonical tensor structure.
  `ContinuousCoefficientCommRing` exports its compatible commutativity instance.
  This uses the existing construction also used by the neighboring root-tower
  statement; it introduces no second definition of coefficients.
- `condensedRingObj Λ T` is the recorded pulled-back coefficient object p_T^*Λ,
  with its transported monoid and commutative-monoid structures.
  `Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u+1}) (condensedRingObj Λ T)` is the
  recorded internal module category, not ordinary constant-coefficient sheaves.
- Y, its structure morphism y to Spec k, `[LocallyOfFiniteType y]` together with
  `[QuasiCompact y]`, `[IsSeparated y]`, and `hY : IsRegularScheme Y` give the
  regular separated finite-type k-scheme. Affine B is `Spec (.of A)`, and
  `b : Spec (.of A) ⟶ Y` with `[Etale b]` gives the affine etale chart.
- The coordinate tuple is `t : Fin r → A`. The reduced SNC boundary is H with
  `hH : IsStrictNormalCrossingsBoundary H`. `hproduct` equates H with the ideal
  sheaf of the product of the t_i (using ΓSpecIso to put the equation in global
  sections). `hbranches` equates the zero loci of the t_i with precisely the
  irreducible components of H's support. These are the same geometric binders
  as the already landed root-tower lisse-morphism-extension interface.
- Affine U is `Spec (.of R)`, the map to B is `Spec.map (CommRingCat.ofHom a)`,
  and its site-morphism condition is `[WeaklyEtale ...]`. This is precisely the
  existing Mathlib small pro-etale site's weakly-etale-object convention.
- The full tower is `Spec (.of (tameRootAlgebra p (fun i ↦ a (t i))))`.
  I read its actual quotient presentation: variables are `(i,n)` for positive
  n coprime to p; the relations are x_(i,n)^n=t_i and
  x_(i,m)^(m/n)=x_(i,n) whenever n divides m. This presents exactly the specified
  filtered colimit, including every transition and all coordinates.
  The projection is written directly as Spec of its canonical algebra map.
- N is universally quantified on that tower, and
  `IsLisseCoefficientModule ... N` is the recorded local finite-free condition.
  Its definition uses a pro-etale covering with `Mod.IsFree` on each pullback;
  that predicate means an isomorphism to a finite biproduct of regular modules,
  with natural-number rank including zero and no fixed global rank.
- A subset is `s : Finset (Fin r)`, which represents every subset of the finite
  coordinate set. `rootCoordinateOpen` is D of the image of the selected product
  in the actual root algebra. It is the displayed T ×_U U[1/product].
- Pro-etale chart changes are quantified by `U'`, `v : U' ⟶ Spec (.of R)` and
  `[WeaklyEtale v]`. The base-changed tower is the actual scheme pullback of
  the explicit canonical Spec map along v, and the coordinate open is its preimage
  under `pullback.fst`. Taking v to be the identity recovers the original tower
  canonically. Allowing nonaffine U' records the statement's arbitrary pro-etale
  base change; it adds no finiteness assumption on that chart.
- `P : Profinite.{u}` is arbitrary, and `(profiniteToProEtOf T').obj P` is the
  recorded T'[P] with its actual projection. `rootTestOpen` takes the inverse
  image of the coordinate open under that projection, canonically identifying
  it with the indicated open's profinite test object. Its `.ι` is j_(A,P).
- The supplied module is pulled back by the composite of the actual parameter
  projection and chart pullback projection. `DerivedCategory.singleFunctor _ 0`
  places that pullback module in degree zero.
- `PunctureUnitAssertions Λ j K` expands to the existence of an isomorphism
  `e : K ≅ Rj_* j^* K` whose hom is *equal to* the specified unit. The right
  adjoint is `moduleObjectDerivedPushforward`, the full unbounded total right
  derived functor from the recorded node. Its left adjoint is the exact termwise
  pullback. `punctureDerivedAdjunction` transports the recorded total derived
  adjunction using `leftDerivedUpperStarIsoMapDerivedCategory`; it preserves the
  actual unit rather than introducing another adjunction by a choice.
- Naturality for maps of the supplied lisse modules is explicit: the predicate
  quantifies arrows f and another normalized unit isomorphism e', and asserts
  both `f ≫ e'.hom = e.hom ≫ Rj_*j^*(f)` and
  `e.inv ≫ f = Rj_*j^*(f) ≫ e'.inv`. Applying the main assertion to any other
  supplied lisse N' provides the required e'. It also permits canonical
  identifications of degree-zero pullbacks and supplied action isomorphisms.
- `punctureSquareComparison` is built from the existing pullback-composition
  isomorphisms and the given square equation. `punctureDerivedExchange` is the
  adjunct of that comparison followed by the pulled-back actual counit.
  `punctureUnitExchange` includes the final inverse comparison so that its target
  is exactly Rj'_*j'^*g^*K. The explicit square equation is
  `g^*(e.hom) ≫ punctureUnitExchange ... K = η'_(g^*K)`.
  Where e' is a normalized unit isomorphism on g^*K, the predicate states that
  this exchange is invertible and `g^*(e.inv) = exchange ≫ e'.inv`.
- Thus maps P'→P use the actual maps of `profiniteToProEtOf`, chart changes use
  the actual pullback projections, and open-preserving automorphisms use their
  actual open squares. For a profinite family Q, use its scheme morphism
  T[P][Q]→T[P], not its individual Q-points. The action isomorphism identifies
  its pullback module with the projection pullback, which the theorem makes
  clean for Q. The module-map and square equations therefore give equality on
  T[P][Q] itself, canonically T[P×Q]. The square assertion quantifies the whole
  scheme T' and whole morphism g; it has no pointwise or finite-quotient test
  replacing this equality. Its formal equation works for every commutative
  square and does not assume an unproved general base-change isomorphism.
- For empty s, the product is 1, so the coordinate open and its two subsequent
  preimages are the whole scheme. `PunctureIdentityAssertions` gives the
  identity-open unit followed by the canonical identity comparisons equal to
  `𝟙 K`, for both coefficient choices. The left comparison is the termwise
  derived `upperStarId`, and the right comparison is its right adjoint mate.
  In the whole-open presentation the source open scheme is canonically
  isomorphic to the ambient scheme rather than definitionally identical.
  The square equation in `PunctureUnitAssertions`, applied to that canonical
  isomorphism and the identity-open square, identifies its unit with this
  normalized identity unit. Thus empty s is included with the identity, not
  merely with an unnormalized existence assertion.

Dependency declarations used (their actual source signatures and docstrings were read):

- `Sheaf.Topology.ContinuousMapCondensedRing`:
  `Profinite.continuousMapRingSheafOfUniverse`, `continuousMapRingObjOfUniverse`,
  and its monoid/commutativity constructions; the same-universe interface is
  `Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse` and
  `ContinuousCoefficientCommRing`, `Profinite.continuousCoefficientRingObj`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`, `profiniteToProEtOf` and its underlying
  profinite-to-scheme construction; these supply the recorded coefficients and
  profinite parameters. `isIso_condensedPullbackHom` is the proof's alpha input.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `ModObj`,
  `Mod.Hom`; `WeilConjectures.CategoryTheory.ModuleObjects.Free`: `Mod.IsFree`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `IsRegularScheme`.
- `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`:
  `IsStrictNormalCrossingsBoundary`.
- `Sheaf.Paper.CoefficientHeartStratificationDefs`: `IsLisseCoefficientModule`.
- `Sheaf.Paper.StrictLocalKummerTameModule`: `TameRootOrder`,
  `tameRootRelations`, `tameRootAlgebra`.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `moduleObjectDerivedPushforward`, together with the upstream
  `derivedUpperStarLowerStarAdjunction` and exact-pullback comparison in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`.
- Proof imports, kept nonpublic: `InternalModuleOperationsTransport`,
  `CondensedClosedSupportAdjunction` (its actual `closedSupport_triangle`),
  `CompositionAdjunctionNormalization`, and
  `RingedSiteModulesGrothendieckOfUniverses`. The supported-coordinate-vanishing
  node has no usable recorded Lean module at delivery time, so its proof import
  cannot yet be supplied. No theorem implementing that independent input is
  needed to *state* the present theorem.

The sole added stmt_dep is the already landed definition node
`def-sfb-strict-local-kummer-tame-module`, which owns the actual root algebra.
The scheme projection uses Mathlib's `Spec.map` on its canonical `algebraMap`;
no auxiliary theorem node is needed. No new node or dependency module is added.
No existing dependency record was repaired or rewritten.

Edge cases checked before and after drafting: s empty gives product 1; r=0
has no variables, no relations and only the empty subset; lisse rank zero is
included by Mod.IsFree; empty P and empty charts are permitted by the schemes,
profinite types and universal binders. Neither a positive rank nor a nonempty
scheme/parameter set nor a cohomological-dimension bound is assumed. No
Noetherian condition is imposed on the infinite tower. All universes and
variables are explicit under `autoImplicit false`; the small pro-etale site
retains object universe u+1 and morphism universe u.

Searches for existing declarations:

- msearch.py leanfinder, query "A lisse continuous coefficient module on the full
  prime to characteristic root tower has invertible derived adjunction unit for
  any coordinate puncture": eight hits, including BDeRham, BDeRhamPlus,
  Algebra.Etale, standard-etale and formal-smoothness declarations; none states
  this assertion.
- msearch.py loogle, query `"root", "tower"`: six hits about polynomial roots,
  AdjoinRoot and scalar towers; none matches.
- msearch.py grep, query
  `(rootTower|tameRootAlgebra|puncture).*(unit|invariance)|unit.*rootTower`:
  one irrelevant `punctured_nhds_smul` hit, no match.
- rg on lean/WeilConjectures and lean/Sheaf for rootTower, root_tower, root tower,
  Kummer towers and puncture: found the existing `tameRootAlgebra`,
  `parameterRootProjection` and the underived lisse Hom theorem; the latter module
  is no longer imported, and the former is unfolded into the canonical Spec map;
  other hits are root-of-unity towers, unit Kummer covers or punctured curves.
  Exact item-id search in WeilConjectures found no declaration.
- Whole-DAG search found the existing strict-local Kummer definition and root
  lisse-morphism-extension node carrying those helpers; there is no new node.
  `tools/blueprint_refs.py search 'root tower'`: zero blueprint-node matches.

Source limitation, preserved from Q03's reviewed split: paragraph (3) is the
blueprint location of the obligation, not an exact all-continuous local
cohomology reference. The source field explicitly says that exact reference is
WANTED. This delivery preserves that field and its proof obligation. There is
no new mathematical counterexample and no statement correction or disputed flag.

Repair self-check: the only mathematical term changed is expansion of the four
occurrences of `parameterRootProjection` to its body from lines 57–59 of the
returned dependency module. The explicit ring map has the same source R and
same target tameRootAlgebra, including r=0 and the zero ring. All four original
proof imports remain because they are modules of recorded proof dependencies,
as required by stages/2-statements.md §3(7); their current lack of use by the
`sorry` proof is expected in stage 2. The identity clause and all other clauses
already accepted by the independent review are retained.

Validation: the saved packet first passed deliver2.py --no-push (commit
b5861a921fe); that automated check did not resolve the independent H2 return.
The repaired file passed scompile.py in both sandbox mode (11.4 s) and actual
library module mode (10.8 s), without errors or warnings. The final delivery
wrapper runs server preflight and per-file compilation again before push.

## Second reading by NY

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
