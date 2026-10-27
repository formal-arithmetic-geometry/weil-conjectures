# Constant-ring realization of the etale/pro-etale square

## Worker report

The module states the node through `coefficients`, `ordinary`, and `derived` in
`AlgebraicGeometry.ProEtale.SfbRingedSquare`. Every theorem has a `sorry` proof.
Definitions contain real constructions. The auxiliary declarations index precisely
four existing sites and four existing site functors, construct the canonical structural
maps, and fix all module comparisons by uniqueness or an adjunction universal property.
There are no new independent notions or dependency replacement modules.

The source was read in `literature/stacks-project/proetale.tex`, lines 4674–4693:
the displayed square precedes lemma-morphism-comparison (09A6). The square there is
for every scheme map; the qcqs hypothesis begins in the subsequent pushforward lemma.
Its inverse-image comparison is the site-object base-change comparison. The module
uses the recorded coefficient-general extension of exactly that comparison.

Hypotheses and clauses, in order:

- Finite discrete commutative A: `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  Discreteness is the fixed-set coefficient interpretation; no topology on A or
  extra nonzero-ring assumption is introduced.
- Arbitrary scheme map p: `{X Y : Scheme.{u}} (p : X ⟶ Y)`. There is no qcqs,
  properness, separation, constructibility, flatness or Tor-dimension binder.
- The four sites in the common universe: `Site X Y .yEt/.xEt/.yPro/.xPro`
  are literally `Y.Etale`, `X.Etale`, `Y.ProEt`, `X.ProEt` with the recorded
  topologies. Their object universe is u+1, Hom universe u. No equality of
  these universes is imposed. These are small relative to the common larger
  universe. `Corner` and `Edge` are finite indices, not replacement sites.
- R_(T,s) = constant A: `RingSheaf A X Y c` is exactly
  `(constantSheaf (topology X Y c) RingCat).obj (RingCat.of A)`.
  RingCat is the forgotten commutative-ring presentation; A is commutative
  and the ring-sheaf operations and all ring maps are unchanged.
- The specified four edges: `siteFunctor p .etale/.proetale/.comparisonX/.comparisonY`
  are the published etale base-change functor, `Scheme.proEtaleBaseChange p`,
  `Scheme.toProEt X`, and `Scheme.toProEt Y`. The continuity instances are existing
  instances, selected by the finite edge index.
- The constant-section-preserving structural maps: `ringDirectMap` is the extension
  of the target-site constant presheaf's sheafification unit, whiskered by the actual
  site functor. `ringMap` is its transpose under the actual Kan-extension/sheafification
  adjunction `ringAdj`. Thus these are specified maps, not arbitrary isomorphisms.
- All four c_w are isomorphisms: the first conjunct of `coefficients` is
  `∀ e : Edge, IsIso (ringMap A p e)`.
- The structural ring equation: the second conjunct of `coefficients` writes its
  two paths in Lean composition order. `supportSiteComparisonCoefficientPullbackIso
  RingCat p` applied to the Y-etale constant ring is c_R. The left path is
  nu_X inverse image of c_(p_et), then c_(nu_X); the right path is c_R, then
  p_proet inverse image of c_(nu_Y), then c_(p_proet).
  Ring-valued morphisms encode preservation of every ring operation. Together with
  the already geometric site edges this is exactly the unbundled commutative ringed
  square; there is no fibre-product-topos or cartesianness assertion.
- The constant-section module equivalences: `restriction` is the existing public
  `constantRingModuleRestriction` at the four original sites. The existing theorem
  `constant_ring_module_sheaves` supplies `restrictionIsEquivalence` and
  `restrictionAdditive`; their bodies merely extract and transport its witnesses.
  The functor restricts scalars along the same constant-section unit and retains
  additive sheaves and all component maps. Its quasi-inverse extends the A-action
  uniquely, so it has the normalization required by the recorded general-site
  constant-ring equivalence. No new module category or arbitrary equivalence is used.
- Actual ringed module operations: `modulePush` is Mathlib
  `SheafOfModules.pushforward` through `ringDirectMap`; `modulePull` is Mathlib
  `SheafOfModules.pullback` for that exact map. `modulePushIsRightAdjoint` supplies
  existence on the original unequal-universe sites. Its docstring gives the
  AsSmall construction and transport of the universal-property adjunction.
  The universal property uniquely determines the pullback up to the precise
  unit-compatible isomorphism used below; this is an allowed adjoint construction.
- Edge identifications: `directComparison_existsUnique` pins the direct-image
  comparison to literal identity functions on every section. `pullComparison_existsUnique`
  pins the pullback comparison by its unit equation with that same direct comparison.
  This equation characterizes the scalar-insertion-normalized ringed pullback;
  it is not a hypothesis supplied by a caller. `directComparison` and
  `pullComparison` select these uniquely determined isomorphisms.
- Actual module commutation comparison: `squareDirectComparison_existsUnique`
  pins the right-image square to identity on `N(X times_Y W)`, for every W and N.
  `moduleSquare` is the conjugate of this exact square under the four actual
  module adjunctions, in the orientation F_X u to v F_Y. Its data is an explicit
  `conjugateIsoEquiv` expression. The section-identity uniqueness condition prevents
  a scalar twist. `ordinary` equates this comparison, under all four
  `pullComparison` maps, with the recorded fixed-A comparison. This equality is
  componentwise for every module sheaf, hence equality of natural maps.
- Preservation of zero, addition and every A-action: `moduleSquare` consists of
  morphisms of the actual module sheaves. After applying `restriction`, its
  components are `ModuleCat A` morphisms, so they preserve zero, addition, and
  every scalar. `ordinary` identifies those exact linear components with the
  specified fixed-coefficient comparison, not just some maps of the same type.
- Ordinary uncompleted derived categories: the derived section and `derived`
  quantify over `HasDerivedCategory.{w}` for each actual module and fixed-coefficient
  category, in a common arbitrary localization universe w. These are the size
  convention's choices of ordinary localization, not extra geometric hypotheses.
  `derivedModulePull`, `derivedFixedPull`, and `derivedRestriction` use exactly
  `Functor.mapDerivedCategory` of the existing exact functors. Explicit named
  instance witnesses inside these definition bodies avoid instance-index inference
  through a reduced corner; none is a file-local instance or a new Abelian structure.
- F_T, u, v and theta: the comparison edges give F_T; `.etale` gives u;
  `.proetale` gives v. `theta` is the exact termwise localization of
  `moduleSquare.symm`, with Mathlib's canonical derived composition identifications.
  All four module functors are exact, so this is their ordinary left-derived square.
- a and theta = a inverse: `a` is `mapDerivedCategorySquareIso` of the recorded
  ordinary fixed-A comparison, in precisely the opposite orientation. `derived`
  compares `theta.hom` with `a.inv`, through the four `derivedPullComparison`
  maps. It quantifies over every derived object K. The naturality already present
  in all the named isomorphisms makes this exactly equality of the specified
  natural isomorphisms under the equivalences. No boundedness/completion condition
  or merely per-degree substitute occurs.

Declaration reuse and imports:

- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`:
  `supportSiteComparisonCoefficientPullbackIso`, the etale/proetale/comparison
  pullbacks and adjunctions, and `supportSiteComparisonSiteBaseChangeIso`.
  Their complete signatures and mate-normalization docstrings were read.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `Scheme.proEtaleSiteComparison`,
  `preservesFiniteLimits_proEtaleSiteComparison`, `proEtaleSiteComparisonModules`.
  This is publicly included by the recorded comparison-coherence module.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`, `constantSheafAdj`,
  and its section-preserving forgetful comparison. The full signatures/docstrings
  of the constant-sheaf and terminal-section adjunction were read.
- `Sheaf.CategoryTheory.SiteModuleSheafConstantRingEquivalence`:
  `site_moduleSheaf_constantRing_equivalence` and
  `site_moduleSheaf_restriction_equivalence`, whose constant and slice normalization
  clauses were read. The canonical public restriction functor is exposed by the
  additional landed dependency `lem-cbc-constant-ring-module-sheaves`, module
  `Sheaf.CategoryTheory.ConstantRingModuleSheaves`, declarations
  `constantRingModuleRestriction` and `constant_ring_module_sheaves`.
  This addition does not modify either existing dependency record.
- `Sheaf.CategoryTheory.RingedToposMorphism`: `RingedToposMorphism` supplies the
  geometric/ringed meaning. The square is expressed using the explicit structural
  ring equation and actual module pushforwards rather than introducing a second
  bundled ringed-topos definition on unequal-universe site presentations.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`:
  `Scheme.proEtaleConstantRingComparison`, module pullback/direct image/adjunction
  and exact derived pullback. These recorded constructions and their constant-unit
  normalizations were read; the four-edge constructions use the same sheaf
  inverse-image and structural-map adjunction recipe in RingCat presentation.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `Etale.DerivedCategoryModule` and ordinary `DerivedCategory` localization.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous`:
  `SheafOfModules.pullback`, `pullbackPushforwardAdjunction`;
  `...PushforwardContinuous`: `SheafOfModules.pushforward`.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `conjugateIsoEquiv`,
  `unit_conjugateEquiv_symm`; `...Adjunction.Basic`: `Adjunction.comp`.
- `WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`:
  `Functor.mapDerivedCategorySquareIso` (built from
  `mapDerivedCategoryNatIso` and `mapDerivedCategoryCompIso`).
- Recorded proof dependencies are imported as proof imports:
  `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`,
  `Sheaf.Paper.RingedTopoiDerivedPullbackIndependent`,
  `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`,
  `Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects`, and Mathlib's
  adjunction/localization modules. Their statements supply the geometric lift,
  tensor pullback, exact localization, and uniqueness arguments in the docstrings.

Edge cases checked mathematically before writing:

- A = 0: no nontriviality or field structure occurs. All section identities and
  adjunction normalizations make sense for the zero module categories.
- X or Y empty: the site and terminal-object constructions remain defined, and
  the statement never chooses a point or assumes a nonempty scheme.
- p = identity: the comparisons remain the published unit-normalized mates,
  including the non-strict chosen site pullbacks; no arbitrary identity substitute
  discards their normalization.
- Disconnected X and locally constant ring sections: equality is detected on the
  constant-presheaf generators after sheafification, not by the incorrect claim
  that every section is globally constant.
- Non-qcqs p: only inverse images are used; the source square precedes the qcqs
  pushforward-comparison assertion. No qcqs restriction is added.
- Unbounded complexes and the zero complex: every derived variable is unrestricted
  in ordinary DerivedCategory, so there is no truncation, D+ inclusion or completion.
- Site universes: original sites keep Type (u+1)/Category u. HasDerivedCategory
  is explicit at the common arbitrary universe w, with no forced universe equality.

Searches (actual results, also retained by msearch in searches.jsonl):

1. msearch leanfinder: “The etale proetale comparison square with constant ring
   coefficients is a ringed square and its derived inverse image comparison is the
   inverse geometric comparison”. Eight results concerned etale ring algebras,
   StandardEtalePair, and the etale forgetful functor; none states this square.
2. msearch loogle: `SheafOfModules.pullbackComp`. Five results gave the generic
   module pullback composition, identity/composition laws and their conjugates.
   They were read in PullbackContinuous.lean; none asserts the specified
   etale/proetale coefficient ring equation and equality with its fixed-A comparison.
3. msearch grep: `RingedTopos|ringed.*square|constant.*[Cc]omparison` in
   Mathlib/CategoryTheory: zero hits.
4. rg over lean/WeilConjectures for the item id: no hits. Concept search
   `ringed.*square|etale.*proetale.*ring|RingedSquareRealization` found only an
   unrelated global ringed-space counit comparison.
5. rg over lean/Sheaf/AlgebraicGeometry for
   `ringed.*square|EtaleProEtaleRingedSquare|ringed.*realization` found the pure
   proetale ringed-square localization/restriction theorems and the consuming
   projection comparison, but no statement of this etale/proetale realization.
   The existing constant-ring module equivalences were reused rather than copied.

No statement change and no STATEMENT-DISPUTED issue. All postponed facts belong
to this node's structural-map, module-identification or derived-localization clauses;
each has the source and the natural-language proof in its docstring.

Validation: the complete module compiled cleanly through scompile.py, in both the
sandbox and actual module modes (about 12 seconds each), before the final proof imports.
The final module and node record are checked again by the required dry run.

## Second reading by Q73

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
