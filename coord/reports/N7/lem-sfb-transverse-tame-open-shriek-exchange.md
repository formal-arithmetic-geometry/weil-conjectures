## Worker report

The module `Sheaf.Paper.TransverseTameOpenShriekExchange` states the geometric exchange,
with the map itself defined by its requested adjunction normalization. No theorem is proved.
All data definitions have real bodies. There are no new DAG nodes or dependency repairs,
and the natural-language node statement is unchanged.

Hypotheses and clauses, individually:

- Distinct primes: `p ℓ : ℕ`, `[Fact p.Prime]`, `[Fact ℓ.Prime]`, `_hpℓ : p ≠ ℓ`.
- The base field: `k : Type u`, `[Field k]`, `[CharP k p]`.
- Norm-topological algebraic closure and finite intermediate field:
  `PadicAlgCl ℓ` and `E : PadicAlgCl.FiniteIntermediateField ℓ`. These are the standard
  chosen algebraic closure with its extended norm, and every finite intermediate field
  inside it. Their topology is the inherited norm topology, not a discrete topology.
- All continuous functions: `continuousCoefficients F` is the existing
  `Profinite.continuousMapRingObj F`. For these `Type 0` coefficient fields it is
  definitionally `continuousMapRingObjOfUniverse.{u,0} F`, including its lifted section
  groups. In particular the Omega coefficient is NOT `padicAlgClRingObj`, whose sections
  are finite-subextension-valued functions. The recorded universe-generalized construction
  and the published construction were read; no new ring construction is introduced.
- Pullback of coefficients: `Modules Λ X` uses exactly `condensedRingObj Λ X`, the
  recorded `p_X^*Λ`, and Mathlib `Mod` for internal modules.
- Ordinary unbounded derived category: every derived object has type `DerivedCategory
  (Modules Λ X)`. `moduleObjectDerivedPushforward` is the total right derived functor
  of the actual module pushforward; no factorwise replacement is made.
- Separated finite-type regular scheme: `Y.Over (Spec (.of k))`, locally finite type,
  quasi-compact and separated structure morphism, and `_hY : IsRegularScheme Y`.
  The other schemes are open subschemes of Y, so their finite-type separated k-structure
  is induced and no independent extra structure is required.
- Reduced SNC divisor and its finite component family: `B : Boundary Y`. Its `divisor`
  and `snc` use the recorded `IsStrictNormalCrossingsBoundary`. `n`, `component`,
  `distinct`, `regular`, `union_eq`, `intersections` are exactly a presentation of the
  witness family in that definition. They add no extra condition on an SNC family.
  The intersection convention includes the empty subset. `outer` is any finite subset
  of that entire family; the inner family is its complement, including empty parts.
- W, V and Y-circle: `B.complement`, `B.outerOpen`, `B.innerOpen` are the complements
  of the indicated closed unions. `_hW`, `_hV`, `_hO` identify the actual open immersion
  ranges with them. The maps `b,a,j,c` have exactly the displayed directions, all are
  open immersions, and `sq : IsPullback b a j c` is the stated cartesian square.
  Using arbitrary isomorphic presentations of these opens avoids equality transports.
- Finite-rank lisse E module: `L : Modules (continuousCoefficients E) W` and
  `_hL : IsLisseCoefficientModule (continuousCoefficients E) L`, using its recorded
  pro-etale locally finite-free definition. Ranks may vary locally and may be zero.
- The exact tameness hypothesis: `_htame : IsStrictLocalKummerTameModule p ...
  B.divisor (b ≫ j) L`. This newly landed dependency quantifies over all geometric
  points and every strict-local boundary parameter tuple, constructs the polynomial
  quotient adjoining ALL positive prime-to-p compatible roots, restricts its spectrum
  to W, and asks for finite constant pullback. Its empty tuple is the identity cover.
  A sandbox draft of this notion was deleted after discovery of the landed node.
- Ordinary L_F: for E the canonical identity-scalar identification gives L itself;
  for Omega the expression is `(Mod.extendScalars (coefficientMap
  (tameBoundaryScalarMap ℓ E) W)).obj L`. This is ordinary balanced tensor, NOT its
  total left derived functor. The inclusion is postcomposition on all continuous maps.
- L_F[0]: `(DerivedCategory.singleFunctor _ 0).obj L_F`.
- Exact b_! and c_!: the recorded `CondensedRing.openImmersionLowerShriek` and their
  exact `mapDerivedCategory` functors; no compactification-dependent lower shriek.
- Canonical restriction rho: `restrictionComparison Λ sq.toCommSq K`. First transport
  exact c^* to the existing derived pullback, then apply the recorded ambient exchange,
  then transport back to exact b^* and remove b^*b_! via the inverse of the actual open
  unit. This is exactly open-slice restriction, rather than an unspecified isomorphism.
  The helper theorems `openUnit_isIso` and `restrictionComparison_isIso` state the
  invertibility needed to use `inv`; their docstrings give the localization proofs.
- Canonical e_F: `exchange Λ sq K` is the inverse rho under the inverse of the
  `derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c` hom equivalence. Its type is
  c_!Ra_*K -> Rj_*b_!K. Thus it is the specified adjunct, with no arbitrary arrow or choice.
- Isomorphism and vanishing for BOTH F: `transverse_tame_open_shriek_exchange` concludes
  the conjunction of `ExchangeAt` for E and for Omega with the ordinary extended L.
  `ExchangeAt` unfolds to `IsIso (exchange ... L_F[0])` and `IsZero` of exact restriction
  of Rj_*b_!L_F[0] to `c.closedComplement`. This is the whole reduced inner union,
  and includes intersections with the outer union, not merely its smooth strata.
- Naturality: `exchange_naturality` states the exact commuting square for every derived
  module arrow; it therefore includes every morphism of the specified L_F in degree zero.
- Scalar restriction: `scalarRestriction`, `directScalarMap`, `shriekScalarIso`, and
  `sourceScalarIso`/`targetScalarIso` are the ordinary scalar-restriction identifications.
  The direct-image arrow is constructed from the ordinary `comapLowerStarIso` and the
  canonical right-derived unit/desc maps. Its invertibility is stated separately using
  the recorded ring-sheaf change adjunction; no extra scalar-flatness assumption is made.
- Explicit coefficient square: `exchange_scalar` states Res(e') after the source
  identification and c_!Ra_*(mu) equals Rj_*b_!(mu) after e. Take
  alpha=`tameBoundaryScalarMap ℓ E` and mu=`scalarUnit ... L` to get exactly the node's
  square. `scalarUnit` is the ordinary extension/restriction adjunction unit x -> 1 tensor x,
  embedded by `singleFunctor` and the exact restriction/single comparison. This clause
  never asserts that extension of scalars commutes with Rj_*.

Dependency declarations used (module, name):

- `Sheaf.Topology.ContinuousMapCondensedRing`,
  `Profinite.continuousMapRingObjOfUniverse`, its published `continuousMapRingObj`
  specialization and `continuousMapRingSheaf` construction.
- `Sheaf.Topology.ContinuousMapCondensedRingMap`, the recorded sectionwise ring maps;
  the same Type-0 map is `continuousMapRingSheafMap` used by `tameBoundaryScalarMap`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`, `condensedRingObj`,
  `coefficientRing`, `coefficientMap` from the published change-of-coefficients module.
- `Mathlib.CategoryTheory.Monoidal.Mod`, `CategoryTheory.Mod`, its action, morphisms,
  and regular module structures; `WeilConjectures.CategoryTheory.ModuleObjects.Free`,
  `Mod.IsFree` (through the lisse and tame definitions).
- `Sheaf.Paper.CondensedModuleDerivedPushpull`, `moduleObjectDerivedPushforward`,
  `moduleObjectDerivedPullback`; the published derived adjunction and exact comparisons.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`,
  `compactificationOverField` and its explicit finite-type/separated setting. No
  compactification choice is used in this open-immersion statement.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`, `IsRegularScheme`.
- `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`, `IsStrictNormalCrossingsBoundary`.
- `Sheaf.Paper.CoefficientHeartStratificationDefs`, `IsLisseCoefficientModule`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`, `IsOpenImmersion`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`,
  `openImmersionLowerShriek`; its derived open adjunction is in
  `...Derived.OpenImmersionLowerShriek`.
- `Sheaf.Paper.StrictLocalKummerTameModule`, `IsStrictLocalKummerTameModule`, with its
  actual root algebra, boundary parameter predicate, and strict-local root projection.
- `Sheaf.Paper.AllContinuousScalarMate`, `tameBoundaryScalarMap`. Only this ordinary
  coefficient map is used; no scalar/direct-image isomorphism is assumed.

Both latter nodes already exist and are added to stmt_deps. Every already stated proof
module is imported. The two currently unstated proof inputs (partial Kummer boundary
unit model and condensed product-action inflation) are named in the proof docstring;
there is no attempt to prove them in this statement-only delivery.

Edge cases checked: n=0 makes both closed unions empty; outer empty or full makes
one open the whole Y; both exchanges reduce under canonical comparisons to the
identity/open-unit exchange. Every r=0 strict-local tuple remains allowed by the
recorded tame predicate. `Mod.IsFree` allows rank zero. The closed restriction is to
the entire inner complement, so no crossing is lost. The empty scheme imposes no
geometric-point requirements. Scheme universes are `u`; geometric-point fields in the
recorded tame interface also range over `Type u`, and coefficients are the canonical
Type-0 padic fields, so there is no independent smaller test universe.

Searches actually run:

- msearch leanfinder: “Transverse tame normal crossing open extension by zero derived
  direct image exchange for continuous ell adic condensed modules”: eight hits, including
  `Condensed.profiniteSolid`, `CondensedMod.IsSolid`, and `ModuleCat.Tilde.toOpen_res`;
  none states the node's exchange.
- msearch loogle: `"Sheaf", "extend", "pushforward"`: zero hits.
- msearch grep: `(tame|transverse).*(pushforward|lowerShriek|extensionByZero)|...`:
  zero Mathlib hits. Repository rg and node-id grep found no matching upstream theorem.
- msearch leansearch: strict-local Kummer-tame module phrase: eight unrelated hits
  including `Module.freeLocus`, `AlgebraicGeometry.Scheme.Modules` and unramified loci.
- Further rg searches of DAG and Sheaf found the exact newly landed
  `def-sfb-strict-local-kummer-tame-module` and its module, which is reused. Blueprint
  search for Kummer returned 52 nodes; ancestor is null for this agent-formulated input.
- Upstream and Sheaf searches found the canonical scalar/pullback helpers and the
  flatness restriction on the older `derivedComapLowerStarIso`; the delivery instead
  defines the canonical right-derived comparison and states its invertibility via the
  existing ring-sheaf change adjunction.

The source paragraph itself cites open-image finiteness and contains no printed tame
proof; the inherited node explicitly marks its all-continuous geometric input as
agent-formulated with exact proof/reference WANTED. The docstring preserves its nine-step
agent proof route. No new counterexample or statement correction was found.

Validation: scompile checked both the sandbox and library module paths; final compile
was warning-free. The deliver2 dry run passed server preflight and per-file compilation.
The six postponed named theorems, all belonging to this node's canonical construction
and assertions, are `openUnit_isIso`, `restrictionComparison_isIso`,
`exchange_naturality`, `directScalarMap_isIso`, `exchange_scalar`, and
`transverse_tame_open_shriek_exchange`. Each has its source/blueprint tag and natural-language
proof docstring. All declarations are recorded in lean.declarations. No unbound implicit
variables, local notation, local instances, or private definitions are introduced.

## Second reading by N7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
