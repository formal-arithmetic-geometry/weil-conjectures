## Worker report

N2, sbc-thm-finite-proetale-smooth-base-change, stage 2, 2026-10-16.

The module states invertibility of the finite pro-etale exchange and the explicit
conjugation identity for every etale model. Its only theorem is
`AlgebraicGeometry.ProEtale.isIso_finite_proetale_smooth_base_change`, with proof
`sorry`. The two remaining definitions have actual data, obtained from already recorded
canonical constructions. No other DAG node is stated or changed.

### Hypotheses and clauses

- Finite discrete commutative coefficients: explicitly bound `Λ : Type (u + 1)`,
  `[CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]` in the section.
  The same coefficients are used on every corner. No nonzero-ring hypothesis is added.
- Positive N, annihilation of Λ, and invertibility on S:
  `(N : ℕ) (hcoeff : Etale.IsSmoothBaseChangeCoefficients N Λ S)`. The imported
  definition is `0 < N ∧ Finite Λ ∧ (N : Λ) = 0 ∧ IsUnit (N : Γ(S, ⊤))`.
- Schemes and maps: `{S T Y X : Scheme.{u}}`, `p : X ⟶ S` (the node's f),
  `g : T ⟶ S`, `e : Y ⟶ T`, `h : Y ⟶ X`.
  `(sq : ChosenCartesianSquare h e p g)` retains the recorded chosen square.
  The exchange uses `sq.toCommSq.flip`, with the source/target roles needed by the
  upstream comparison interface. No arbitrary comparison of inverse images is supplied.
- All four corners noetherian: four separate `IsNoetherian` instances, for
  X, Y, S, T. Mathlib's IsNoetherian is locally noetherian and quasi-compact,
  equivalently the node's finite affine cover by noetherian spectra.
- Smooth f and qcqs g: `[Smooth p] [QuasiCompact g] [QuasiSeparated g]`.
  The target-comparison definition obtains qcqs h using the chosen pullback
  identification and Mathlib's `MorphismProperty.of_isPullback`; it is not added as a hypothesis.
- Constant ring coefficient category and etale origin: K is an actual
  `FiniteCoefficientDerivedCategory T Λ`, and
  `hK : isBoundedConstructibleFiniteCoefficient T Λ K` is exactly the dependency's
  essential-image predicate, not a newly copied constructibility predicate.
- The first conjunct asserts IsIso of the canonical ambient exchange in
  `FiniteCoefficientDerivedCategory X Λ`. It is written by computing the existing
  `derivedBaseChangeMap` at the canonical inverse-realization coordinates of K,
  then applying `(finiteCoefficientRealization X Λ).mapDerivedCategory` to its arrow.
  Thus the conclusion remains an arrow in the recorded ringed module category.
  The source and target are ordinary uncompleted operations in canonical
  fixed-scalar coordinates. Realization is sheafification along constant scalar
  sections; it identifies their actions with the recorded constant-ring structure
  maps. Transport of the specified unit--square--counit mate through this equivalence
  is the ringed ambient mate. No arbitrary arrow or mere existence of an endpoint
  isomorphism is substituted for it.
- The second conjunct quantifies over *every* bounded constructible L and
  *every* `α : finiteCoefficientDerivedComparison T Λ (ι.obj L) ≅ K`.
  L is represented as a bounded-below object with
  `_hL : Etale.DerivedCategory.isBoundedConstructible Λ T (ι.obj L)`;
  every bounded constructible etale complex has this representation.
  `finiteSmoothModelCoordinates` expresses the actual supplied ringed α in the
  inverse-realization coordinates: realization unit, inverse of the canonical
  exact-functor composition comparison, then the given α.
  The equality's right side is, in Lean's composition order:
  source functor applied to α inverse; `baseChangeSourceComparisonIso.inv`;
  derived site image of `Etale.baseChange`; `finiteSmoothTargetComparison.hom`;
  target functor applied to α. The whole composite is realized back into the
  recorded ringed category. This is precisely the node's conjugation formula.
- Neither endpoint is asserted bounded or constructible. Only the input K and
  the chosen etale model carry the corresponding predicates.

### Dependency declarations read and used

Read all ten statement-dependency nodes, their complete statements and Lean records,
and the recorded declarations with their docstrings. Direct recorded modules are
imported (convention-only scheme node has no module). Definitions and maps used are:

- `Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients`:
  `AlgebraicGeometry.Etale.IsSmoothBaseChangeCoefficients`.
- `Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso`:
  the chosen-square and inverse-image interfaces. `IsPullback` presents the same
  cartesian square, with the opposite pair of projection roles needed for exchange.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`;
  Mathlib `QuasiCompact`, `QuasiSeparated`, `IsNoetherian` for scheme conventions.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `FiniteCoefficientDerivedCategory`, `finiteCoefficientRealization`,
  `finiteCoefficientDerivedComparison`, `isBoundedConstructibleFiniteCoefficient`.
  In particular the realization equivalence is the dependency's specified
  sheafification construction, not an independently chosen equivalence.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`:
  the scalar-preserving coefficient map and its constant-sheaf normalization.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations` publicly retains
  `ProEtaleFiniteCoefficientDirectImage` and the arbitrary identified-ring operations.
  These supply ordinary, uncompleted operations and realization; no completed
  or intrinsic-small-coefficient replacement is used in the theorem.
- `Sheaf.Paper.PbcActualRingedExchange` publicly retains
  `Scheme.proEtaleAmbientRingedExchange`, the mate of the canonical composition
  comparison under the specified derived adjunctions. The fixed-scalar
  `derivedBaseChangeMap` is the same mate in realized coordinates.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparisonModules` and the reexported comparison inverse image.
- `Sheaf.AlgebraicGeometry.BoundedDerivedSmoothBaseChange`:
  `Etale.isIso_derivedBaseChangeMap_of_boundedConstructible_of_smooth` for the proof.
- `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange`:
  `baseChangeSourceComparisonIso`, `baseChangeTargetComparisonIso`,
  `comparison_derivedBaseChangeMap`. Their full signatures and constituent
  canonical comparison maps were read, as was `derivedBaseChangeMap` in
  `Derived.UpperLowerStar` (literally `mateEquiv` of the derived square comparison).
- Proof imports also retain the stated base-change-map, direct-image comparison,
  and pullback-coherence modules. The statement docstring follows all five DAG
  proof steps, including qcqs permanence, the named transport identity, and naturality.

### Edge cases

The empty scheme at any corner, zero coefficient ring, and zero complex are included.
For N = 0 the coefficient hypothesis is false; for N = 1 the coefficient ring is the
zero ring and is allowed. No nonempty scheme or nonzero coefficient hypothesis appears.
All schemes have universe u; coefficient rings and module values have universe u+1.
Site object and morphism universes are not equated. Identity squares and arbitrary
model isomorphisms, including identity α, use the same canonical unit and composition
comparison. No lift of a model is selected by an arbitrary existence witness.

### Searches and reuse

The preserved searches.jsonl records msearch.py queries and results:

- leanfinder: "smooth base change for bounded constructible pro etale complexes with
  finite invertible coefficients"; eight algebraic smooth/etale base-change hits,
  no full derived sheaf exchange theorem.
- loogle: `AlgebraicGeometry.ProEtale.derivedBaseChangeMap`; no remote index hit
  (unknown identifier there). Repeated with `CategoryTheory.Sheaf, DerivedCategory`:
  zero hits.
- grep: `smooth.*base.?change|base.?change.*smooth`, AlgebraicGeometry/Sites;
  no hit in Mathlib.
- rg of WeilConjectures and lean/Sheaf, plus the exact blueprint id, found the
  existing upstream invertibility theorem. It states fixed-scalar invertibility
  alone and omits the node's explicit for-every-model conjugation conclusion and
  its four noetherian corner hypotheses, so it is not an exact existing attachment.
  Its map, comparisons, and realization constructions are reused without copying.
- Exact helper-name searches found no previously declared finiteSmooth* helpers.

The current blueprint paragraph and proof were read in
`literature/blueprint/main-20261015/blueprint/sec-smooth-base-change/sk-thm-sbc-coefficients/`.
The reviewed DAG already makes the finite coefficient and etale-origin scope precise;
no mathematical statement correction or STATEMENT-DISPUTED claim is made.

### Validation and repair of the retained attempt

The former global overlay duplicate-declaration failure no longer reproduces.
The old statement first compiled, but inspection found its omitted conjugation clause,
wrong input presentation, and missing docstring tag. These were repaired in the module
above; the report no longer claims the obsolete compile-tool failure.

The complete revised module compiles cleanly through scompile.py in both its sandbox
and library module paths (6.9 s and 7.3 s respectively on the final run, default
60-second limit).
No theorem is proved. The delivery is for the independent second reader; nothing is pushed.

## Earlier second reading (a previous round; superseded)

Independent second reading, 2026-10-16. I read the reviewed DAG statement and all
five proof steps, the blueprint source at
`sec-smooth-base-change/sk-rem-rest/sbc-thm-finite-proetale-smooth-base-change.md`,
the coefficient conventions, and Stacks `etale-cohomology.tex`,
`theorem-smooth-base-change` (0EYU) and `lemma-smooth-base-change-general` (0F09).
The latter explicitly assumes smooth pullback, qcqs direct image and allowable
torsion; it does not assume finite dimension or impose an upper output bound.
The reviewed node adds the four noetherian corners and specializes to finite
coefficients and etale-origin objects. Those assumptions have been retained.
There is no statement_change and no new node or dependency module in this delivery.

Here is my independent object/hypothesis/conclusion list and the final Lean match.

| Node component | Final Lean rendering and verdict |
| --- | --- |
| One finite discrete commutative coefficient ring on every corner | Section binders `Λ : Type (u + 1)`, `[CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]`. All operations use exactly this Λ. Match. |
| Positive annihilator N and invertibility on S | `(N : ℕ)` and `hcoeff : Etale.IsSmoothBaseChangeCoefficients N Λ S`. I opened its definition: `0 < N ∧ Finite Λ ∧ (N : Λ) = 0 ∧ IsUnit (N : Γ(S, ⊤))`. Match. |
| Four schemes S,T,Y,X and edges f,g,e,h | `{S T Y X : Scheme.{u}}`, `{p : X ⟶ S}`, `{g : T ⟶ S}`, `{e : Y ⟶ T}`, `{h : Y ⟶ X}`. Lean p is the node's f. Match. |
| Cartesian square with the dependency's chosen identification | Repaired to `sq : ChosenCartesianSquare h e p g`, the exact object in `sbc-def-base-change-square`. Its fields retain commutativity and a projection-compatible `Y ≅ pullback p g`. `sq.toCommSq.flip` is the same square in the exchange API's orientation. Match after repair. |
| Noetherian at every corner | `[IsNoetherian X] [IsNoetherian Y] [IsNoetherian S] [IsNoetherian T]`. I opened Mathlib: the class extends `IsLocallyNoetherian` and `CompactSpace`, equivalent to the node's finite noetherian affine covering. No finite-dimensional assumption. Match. |
| Smooth f | `[Smooth p]` from the exact recorded Mathlib module; not smooth-at-a-point or merely formal smoothness. Match. |
| qcqs g | `[QuasiCompact g] [QuasiSeparated g]`. The helper derives qcqs h using `IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd`, flips that proof, and applies `MorphismProperty.of_isPullback`. No extra hypothesis on h. Match. |
| The constant continuous-function coefficient ring and its ambient derived module category | `FiniteCoefficientDerivedCategory W Λ` is the dependency's localization of `ringedSiteModules (finiteCoefficientRingSheaf W Λ)`; I read the sheafified continuous-function construction and scalar sections in `ProEtaleFiniteModules`. The map is expressed through its canonical exact realization equivalence, preserving this ambient ringed category. Match. |
| Input K in the strictly full bounded constructible etale essential image | `K : FiniteCoefficientDerivedCategory T Λ` with `hK : isBoundedConstructibleFiniteCoefficient T Λ K`. I read its `ObjectProperty.map` body: the model has a finite cohomological interval and a finite constructible stratification with finite constant module values on an etale trivializing cover. Match; no arbitrary pro-etale essential-surjectivity assumption. |
| Ordinary uncompleted ambient exchange is invertible | The first conjunct is `IsIso` of realization applied to the specified upstream `derivedBaseChangeMap` at inverse realization of K. I opened its definition: it is literally the mate of `leftDerivedUpperStarSquareIso` under `derivedUpperStarLowerStarAdjunction`, hence retains the unit, canonical square comparison, and counit, rather than any endpoint isomorphism. This is the constant-scalar coordinate presentation also used by the recorded `lem-weil-pbc-transport-identifies-exchange`. No completion or reflector occurs. Match in the canonical coefficient presentation. |
| Every bounded constructible etale model L and every specified alpha | The second conjunct is `∀ L : DerivedCategory.Plus ..., ∀ _hL : Etale.DerivedCategory.isBoundedConstructible ... (ι.obj L), ∀ α : finiteCoefficientDerivedComparison ... (ι.obj L) ≅ K, ...`. A bounded model is bounded below; using Plus neither drops a bounded model nor strengthens its mathematical bound. Match. |
| Canonical conjugation formula, including alpha | The equality is realization of `F_K = source(β⁻¹) ≫ S_L⁻¹ ≫ ν_X(E_L) ≫ T_L ≫ target(β)`, where β is exactly `finiteSmoothModelCoordinates Λ T K L α`. That helper is the derived realization unit followed by the inverse image of the canonical exact-composition comparison and the supplied α. I checked all directions against the five proof steps. `baseChangeSourceComparisonIso g p Λ` and the target comparison have the required S_L,T_L signatures. Match. |
| No bound or constructibility asserted for either endpoint | The conclusion contains no endpoint predicate. Only K and the etale model L carry the relevant predicates. Match. |

I opened the signatures and bodies needed from all ten statement dependencies:
`SmoothBaseChangeCoefficients`, `BaseChangeInverseImageIso` and
`ChosenCartesianSquare`, Mathlib smoothness and qcqs, `ProEtaleFiniteModules`,
`ProEtaleConstantRingMap`, `ProEtaleIntrinsicFiniteOperations` and its retained
`ProEtaleFiniteCoefficientDirectImage`, `PbcActualRingedExchange` and its retained
`ProEtaleAmbientRingedExchange`, `ProEtaleSiteComparison`, and
`BoundedDerivedSmoothBaseChange`. In particular I distinguished the finite
RingCat-module presentation from the arbitrary compatible CommRingCat ringed
square interface. The statement uses the canonical finite coefficient realization,
not a bare type equivalence or a chosen unrelated map. The constant-ring-map theorem
normalizes that realization on scalar sections. The recorded transport dependency
uses this same fixed-scalar mate presentation. The source/target comparisons in the
upstream `SmoothBaseChange` module were checked with `(f,g,g',f')=(g,p,e,h)`.

The quantified etale predicate is the project's finite-value stratification predicate
`Etale.DerivedCategory.isBoundedConstructible`, not the upstream predicate with a
similar name. I read `BoundedConstructibleComplexes` and
`IsConstructibleEtaleModuleSheaf` and matched their finite module values and interval
to the inline essential-image predicate in `ProEtaleFiniteModules`.

Edge cases: the zero ring, empty schemes, zero complexes, and empty strata are allowed.
There is no `Nontrivial`, `Nonempty`, integral, field, separated, finite-dimensional,
or finite-type hypothesis. N=0 makes the positive coefficient hypothesis false;
N=1 allows precisely the zero coefficient ring. Characteristic restrictions are
exactly `(N : Λ)=0` and invertibility on S. Identity squares and identity alpha are
included; arbitrary alpha uses the same realization unit and composition comparison.
Schemes have universe u, scalar rings and section values have universe u+1, in the
recorded site's size convention. No equality of object and morphism universes or
independent undersized index universe is imposed. `autoImplicit false` binds all
variables; the final source has no hidden statement `let`, `show ... from`, private
copy, local notation, or local instance declaration.

Independent H4 searches, using wording different from the writer:

- `msearch.py leanfinder`: “etale inverse image of finite coefficient complexes
  commutes with derived direct image after smooth base change with canonical exchange
  conjugation”. Eight hits, all etale/smooth ring-map stability or differential
  comparisons; none is the complete derived exchange and conjugation assertion.
- `msearch.py loogle`: `CategoryTheory.IsIso, AlgebraicGeometry.Smooth`. One hit,
  `Scheme.Hom.instIsIsoNormalizationPullbackOfSmooth`, about normalization. Not a match.
- `msearch.py grep`: `exchange|derivedBaseChange|boundedConstructible` in
  `AlgebraicGeometry/Sites`. Zero Mathlib hits.
- Direct `rg` through Mathlib, the slopmaster2 source, the read-only pro-etale framework,
  and `lean/Sheaf`, with `comparison_derivedBaseChangeMap`,
  `isIso_derivedBaseChangeMap_app_of_smooth`, the blueprint id, and realization and
  comparison helper names. I read the upstream invertibility theorem: it has only
  `IsIso` in fixed-scalar coordinates, omits the second conjunct, and has fewer
  hypotheses. It therefore does not give an exact existing binding of this node.
  Its mate, comparisons and model transport are reused. The published refinement
  module already uses `mapDerivedCategory.asEquivalence`; a second named derived
  realization equivalence is unnecessary here.

Mismatches found and repaired:

1. The source accepted only `IsPullback e h g p`, losing the dependency's explicit
   chosen-square input. It now accepts `ChosenCartesianSquare h e p g`, uses its
   flipped commutative square for both exchanges, and obtains the target's qcqs
   instances from the actual projection-compatible pullback identification.
2. Removed `finiteSmoothDerivedRealization`, which merely wrapped an existing
   equivalence construction. All coordinates now use
   `(finiteCoefficientRealization T Λ).mapDerivedCategory.asEquivalence` directly.
   There are two remaining data helpers, and `lean.declarations` records exactly them
   and the theorem.
3. Updated `lean.statement` verbatim from the final theorem signature and corrected
   the worker report's descriptions of the square and helper count. The mathematical
   node statement and dependencies are unchanged.

The source/blueprint docstrings remain complete and the theorem docstring follows
all five DAG proof steps. The only theorem has proof `sorry`; the two definitions
have actual data, including a real proof of the derived qcqs instances. No hollow
choice or additional postponed theorem is introduced. The revised file compiled
cleanly through `scompile.py` in sandbox and library paths, with the default 60-second
limit, nice 19, and two threads. The subsequent delivery dry run reruns compilation
and the maintainer's preflight on the current base.

## Second reading by N2

Independent delivery reading, 2026-10-16. I read the current sandbox module and
node, all ten statement-dependency nodes and their recorded source declarations,
the five proof steps, the original and main-20261015 blueprint paragraphs, and
Stacks `etale-cohomology.tex`, labels `theorem-smooth-base-change` (0EYU) and
`lemma-smooth-base-change-general` (0F09). The first has smooth pullback, qcqs
direct image and stalkwise allowable torsion. The second gives the bounded-below
derived version, also allowing a directed limit of smooth base changes. Neither
requires finite dimensionality or bounded constructible outputs. The reviewed
node specializes to finite coefficients and four noetherian corners; the Lean
retains these hypotheses. No statement correction is needed or made.

My object, hypothesis and conclusion list, matched against the Lean:

| Node component | Lean rendering and verdict |
| --- | --- |
| One finite discrete commutative ring Lambda on all corners | Section variable `Λ : Type (u + 1)` with `CommRing`, `Finite`, `TopologicalSpace`, `DiscreteTopology`. Every construction uses this same ring. Match. |
| Positive N, N annihilates Lambda, N invertible on S | `N : ℕ`, `hcoeff : Etale.IsSmoothBaseChangeCoefficients N Λ S`. Its opened definition is `0 < N ∧ Finite Λ ∧ (N : Λ) = 0 ∧ IsUnit (N : Γ(S, ⊤))`. Match. |
| Four schemes and the four specified arrows | `{S T Y X : Scheme.{u}}`, `{p : X ⟶ S}`, `{g : T ⟶ S}`, `{e : Y ⟶ T}`, `{h : Y ⟶ X}`. Lean p denotes the node's f. Match. |
| Cartesian square with chosen identification | `sq : ChosenCartesianSquare h e p g`. I read its `isoPullback`, `hom_fst`, `hom_snd` fields and inherited commutativity. Flipping `sq.toCommSq` gives exactly the exchange orientation `(g,p,e,h)`. Match. |
| Each corner admits a finite noetherian affine cover | Four instances `IsNoetherian X`, `IsNoetherian Y`, `IsNoetherian S`, `IsNoetherian T`. Mathlib's class is locally noetherian plus compact; its finite affine cover characterization immediately follows in `Noetherian.lean`. Match. |
| Smooth f | `[Smooth p]`. I opened Mathlib's affine-chart smooth-ring-map definition and the dependency's recorded match. No relative dimension or additional finiteness assumption is added. Match. |
| Quasi-compact and quasi-separated g | `[QuasiCompact g] [QuasiSeparated g]`. `finiteSmoothTargetComparison` derives both instances for h from `IsPullback.of_iso_pullback` and base-change permanence. They are not independent hypotheses. Match. |
| Continuous-function constant ring on each small pro-etale corner | `FiniteCoefficientDerivedCategory W Λ`, through `finiteCoefficientRingSheaf`, is localization of module sheaves over the sheafified continuous-function presheaf on connected components. I read that construction, its constant scalar map and the associated-module-sheaf realization. Match. |
| Canonical structure maps of the coefficient-ring node | `finiteCoefficientRealization` uses `finiteCoefficientScalarMap`. The opened constant-ring-map module constructs rho by projection precomposition, takes its adjunct c, and identifies it with the constant-preserving structure map. The fixed-scalar operations therefore present the specified coefficient actions. Match. |
| K belongs to the strictly full bounded constructible etale essential image | `K : FiniteCoefficientDerivedCategory T Λ`, `hK : isBoundedConstructibleFiniteCoefficient T Λ K`. I read its `ObjectProperty.map` body and compared it to `Etale.DerivedCategory.isBoundedConstructible` and `Scheme.IsConstructibleEtaleModuleSheaf`: finite strata, finite constant module values on etale covers, and a finite cohomological interval agree. Match. |
| Ordinary uncompleted canonical ambient exchange at K is invertible | First conjunct: `IsIso` of realization applied to `derivedBaseChangeMap ... sq.toCommSq.flip` at the inverse realization of K. Its opened definition is `mateEquiv` of `leftDerivedUpperStarSquareIso` under the specified derived pullback/direct-image adjunctions. The square comparison is inverse composition, commutativity, then composition. Transport by constant-scalar realization is the ringed mate, with the same normalization as the recorded transport-identifies-exchange declaration. No completion occurs. Match. |
| Every bounded constructible etale model L | `∀ L : DerivedCategory.Plus ..., ∀ _hL : Etale.DerivedCategory.isBoundedConstructible ... (DerivedCategory.Plus.ι.obj L)`. A bounded complex is bounded below, so this represents every model in the node. Match. |
| Every specified model isomorphism alpha | `∀ α : finiteCoefficientDerivedComparison T Λ ... ≅ K`. `finiteSmoothModelCoordinates` uses this exact alpha, the realization unit and the canonical `Functor.mapDerivedCategoryCompIso`; no unrelated lift or existential choice replaces alpha. Match. |
| The canonical conjugation identity | The second conjunct says `F_K = source(β.inv) ≫ S_L.inv ≫ ν_X(E_L) ≫ T_L.hom ≫ target(β.hom)`, followed by realization. Here β is `finiteSmoothModelCoordinates ... α`. I opened both upstream comparison isomorphisms: S first compares pullback, then direct image; T first compares direct image, then pullback. Their orientations and the inverse of S agree with DAG proof steps 3--5. E is `Etale.baseChange` on this same flipped square, not an arbitrary endpoint isomorphism. Match. |
| No boundedness or constructibility of either endpoint | Only K and L have the corresponding predicates; both sides of the exchange live in the ambient unbounded category. Match. |

Dependency inspection included `ProEtaleFiniteModules`, `ProEtaleConstantRingMap`,
`ProEtaleIntrinsicFiniteOperations` and its retained
`ProEtaleFiniteCoefficientDirectImage`, `PbcActualRingedExchange` and its retained
`ProEtaleAmbientRingedExchange`, `ProEtaleSiteComparison`,
`SmoothBaseChangeCoefficients`, `BaseChangeInverseImageIso`,
`BoundedDerivedSmoothBaseChange`, and the exact read-only pro-etale framework's
`BaseChange.SmoothBaseChange` and `Derived.UpperLowerStar`. I distinguished the
arbitrary compatible ring-sheaf interface from its constant-coefficient module
presentation, and the project's finite-value constructibility predicate from the
similarly named upstream predicate. I also read `coord/pefw-upstream-framework.md`.
There are no new definition nodes or dependency modules in this delivery.

Edge cases: empty schemes, empty strata, the zero ring and zero complex are
allowed. There is no nontriviality or nonemptiness assumption. N=0 is excluded
exactly by the positive-annihilator convention; N=1 allows the zero ring. The
characteristic condition is exactly annihilation by N and invertibility on S.
Identity squares and identity alpha are included, and an arbitrary alpha uses
the same unit and composition comparison. All schemes have universe u; the
coefficient ring and module values have universe u+1, as in the dependency's
small-site convention. Object and morphism universes are not equated. There is
no independent undersized index universe. `autoImplicit false` and the explicit
universe binder leave no unbound variable or universe.

Fresh independent H4 searches (recorded in `searches.jsonl`):

- LeanFinder: "canonical smooth exchange for derived torsion sheaves together
  with compatibility under etale to proetale comparison and every model
  isomorphism". Eight hits concern etale/smooth ring maps, differentials or the
  forgetful functor of the etale site; none states the exchange assertion.
- Loogle: `CategoryTheory.IsIso, CategoryTheory.NatTrans`. Zero hits.
- Mathlib grep through msearch: `proEtaleAmbientRingedExchange|finiteSmooth|comparison_derivedBaseChangeMap`.
  Zero hits.
- Direct `rg` in Mathlib, slopmaster2, the read-only framework and `lean/Sheaf`
  for the helper names, the theorem name, `comparison_derivedBaseChangeMap` and
  `isIso_derivedBaseChangeMap_app_of_smooth`. The existing upstream invertibility
  theorem is fixed-scalar only and has no every-model conjugation conjunct. Its
  separate transport theorem supplies the canonical comparison used here, not
  an exact existing attachment of the complete node. No duplicate helper was
  found. Existing maps and comparisons are reused.

No further mismatch was found in the current source. The earlier reading's
chosen-square and redundant-equivalence repairs are present and correct; I did
not rewrite them. This reading changes only this report. The sole theorem has
proof `sorry`; both helpers contain real data. Every declaration has its source
and blueprint docstring, and the theorem docstring follows all five DAG steps.
The node's `lean.statement` was mechanically checked verbatim against the source
signature; the declared names, one-module ownership and 100-column limit agree.

Validation: the prescribed `scompile.py`, run from the sandbox, passed without
errors or warnings. It checked the current overlay dependency and compiled the
delivered file separately in sandbox and library paths (10.2 s and 12.4 s), under
the unchanged 60-second limit. The initial invocation from the read-only project
directory could not resolve the sandbox-relative path; rerunning from the correct
directory resolved that invocation error without changing any source.
