## Worker report

The delivery states `CategoryTheory.RingedRestrictionLimit.ringedRestrictionStrictLimitCoherence`
in `Sheaf.Paper.RingedRestrictionStrictLimitCoherence`. Its only postponed proof is this
theorem, whose docstring supplies the complete eight-step natural-language proof from
the node. All helper definitions have real data; their source and blueprint references
are in their docstrings. No existing declaration found states this result.

The source read was the current blueprint,
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-sf-comp-coherence/det-sf-comp-coherence-refinement.proof.md`,
the integral comparison in refinement (2), together with the node's proof and recorded
dependencies. The mathematical statement and proof fields of the node are unchanged.

### Hypotheses and clauses

* Sites small in one common universe: `C D : Type u`, `[SmallCategory C]`,
  `[SmallCategory D]`, and topologies `J K`. Terminal objects are the explicit
  `[HasTerminal C] [HasTerminal D]` hypotheses in the statement section.
* Commutative ring sheaves: `R : Sheaf J RingCat.{u}` and
  `S : Sheaf K RingCat.{u}`, with pointwise commutativity `_commR`, `_commS`.
  The use of `RingCat` follows the dependency interface; these explicit hypotheses
  retain commutativity rather than silently discarding it.
* Geometric morphism, pulled-back coefficients, identity structural map, and exact
  module inverse image: `x : UnboundedExactTower.ExactMorphism S R` is the existing
  interface containing the ringed geometric morphism, invertible structural ring map,
  induced inverse-image functor, and its adjunction to `x.ringed.modules`. An invertible
  structural map identifies the chosen presentation `S` with the inverse image of `R`;
  under that identification the structural map is the identity. This merely allows a
  chosen presentation of the pullback sheaf. No arbitrary inverse-image map is added.
* Exact countable products on both module categories are precisely the two
  `HasExactLimitsOfShape (Discrete ℕ)` instances. Product preservation is
  `PreservesLimitsOfShape (Discrete ℕ) x.inverse`.
* Module sheaves use the existing transparent `ringedSiteModules` abbreviation.
  Ordinary unbounded derived categories use `DerivedCategory.{w}`; all six explicit
  `HasDerivedCategory.{w}` instances choose realizations of these categories. There
  is no boundedness, connective, or bounded-below condition.
* `L_B`, `L_B'`, `L_Z` are `limitFunctor ... |>.rightDerivedFunctor`. The underlying
  functor is the existing ordinary strict tower limit, not the limit of a diagram
  of objects of a derived category. The index is `ℕᵒᵖ` (Lean index `op n` denotes
  paper level `n+1`).
* Actual sections are `sections R` and `sections S`: forget the module structure
  to an abelian sheaf, then evaluate at the terminal object. Their
  `rightDerivedFunctor`s are the stated `H_B` and `H_B'`. No substitute cohomology
  functor is supplied as a hypothesis.
* `c` is the ordinary sections/direct-image comparison. `IsSectionsComparison`
  fixes it on every section by the given geometric adjunction, using the actual map
  from the singleton sheaf associated with a global section. Thus it is not an
  arbitrary isomorphism between the relevant functors.
* `rho` is a natural transformation with the required endpoints.
  `IsRestriction` requires its K-injective computation to be sections applied to
  `G(v) η`, followed by `c`, for every K-injective pair and every quasi-isomorphism
  `v : F I ⟶ T`. This is the actual derived adjunction unit and canonical
  composition comparison. Its equation retains the derived units and localization
  factor isomorphisms, so it does not identify an arbitrary restriction map with
  the canonical one by an unsupported choice.
* `rhoT` has the derived strict-tower endpoints. Its `IsRestriction` uses
  `x.adjunction.whiskerRight ℕᵒᵖ` and the actual termwise `c`. The explicit
  evaluation equation identifies every evaluated `rhoT` with `rho`; the
  `IsEvaluationComparison` conditions normalize both evaluation isomorphisms by
  their derived units and require compatibility with every index morphism. Thus
  the whole strict tower, including all transitions, is retained.
* `lambda` is an isomorphism with the required orientation.
  `IsInverseLimitComparison` is the normalized resolution formula: apply inverse
  image to the source derived-limit unit, then compare to the target resolution;
  this equals the ordinary `limit.post` comparison followed by the limit of the
  quasi-isomorphism and the target derived-limit unit. This is the normalization
  in `exactProductFunctorStrictLimit`.
* `aR` and `aS` are isomorphisms with the displayed endpoints.
  `IsLimitComparison` fixes each by the common underived-composite equation,
  using `limit.post` and the derived units of the three functors. This is the
  normalization of `ringedTowerPushforwardLimitComparison` applied to sections.
  It does not assume that sections preserve K-injectives.
* The penultimate conjunction, quantified over every derived strict tower `M`,
  is exactly
  `rho.app (L_R.obj M) ≫ RH_S.map (lambda.hom.app M) ≫ aS.hom.app (F_T.obj M)
    = aR.hom.app M ≫ L_Z.map (rhoT.app M)`.
  Composition is written left-to-right in Lean. Every constituent is a natural
  transformation or natural isomorphism, so this is natural for all morphisms
  in the derived category, not only cochain maps between chosen representatives.
* The last conjunction quantifies over every strict tower complex `X`, every
  complex `P`, and every compatible strict augmentation `gamma`. It compares
  the actual source augmentation followed by the bottom route with the actual
  inverse-image augmentation followed by restriction and the upper comparison.
  Both use the existing `roosAugment` and the same normalized `theta`, `thetaS`
  as fixed by `IsRoosComparison`. In the native cone coordinates `roosAugment`
  is `(0, gamma)` (shifted product first); in the paper's signed product-first
  coordinates it is `(gamma, 0)`. In particular the shifted-product coordinate
  is zero. The normalization equation uses the ordinary-limit inclusion on
  K-injective complexes with injective terms, so these are the specified Roos
  comparisons, not arbitrary isomorphisms with the same endpoints.
* Neither `rho` nor `rhoT` has an `IsIso` hypothesis or conclusion. Only the
  comparisons which the node calls isomorphisms are isomorphisms.

### Dependency declarations used

The original statement dependencies were read at their recorded declarations:

* `Sheaf.CategoryTheory.SiteCoveringAxioms`, `Precoverage.IsSiteForCoverings`;
  sites themselves use Mathlib `GrothendieckTopology` and `Sheaf`.
* `def-weil-size-convention` is a metatheory convention; the common `u` and
  explicit independent derived localization universe `w` implement it.
* `Sheaf.CategoryTheory.RingedToposMorphism`, `CategoryTheory.RingedToposMorphism`.
* `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory` and
  `HasDerivedCategory` (the abstract-derived-category node's Mathlib match).
* `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`,
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`.
* `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`,
  `Functor.rightDerivedFunctorOfQuasiIsoResolutions`, its unit and universal
  property. For these Grothendieck categories the existing
  `Functor.rightDerivedFunctor` is a representative of that same total derived
  functor; `UnboundedExactTower.cochainUnit` supplies its actual cochain unit.
* `Sheaf.Paper.ExactProductFunctorStrictLimit`,
  `CategoryTheory.exactProductFunctorStrictLimit`, especially the resolution
  normalization and strict augmentation clauses.
* `Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison`,
  `CategoryTheory.ringedTowerPushforwardLimitComparison`, especially its
  underived-composite unit equation and projection normalization.

The actual APIs reused now have definition owners in `stmt_deps`:

* `def-sfb-exact-ringed-module-inverse-image` owns
  `Sheaf.CategoryTheory.UnboundedExactAdjunctionSquare`'s
  `CategoryTheory.UnboundedExactTower.ExactMorphism`, `moduleResolutions` and
  `towerResolutions`. Its fields are the actual ringed morphism, structural-map
  invertibility, additive exact inverse image, and adjunction to the module direct image.
* `def-pur-tower-derived-localization-comparisons` owns the same module's
  `CategoryTheory.UnboundedExactTower.cochainUnit`. The `unit` abbreviation uses it.
* `def-sfb-strict-tower-limit-functor` owns
  `Sheaf.CategoryTheory.TowerLimitTransposeNormalization`'s
  `CategoryTheory.TowerLimitTransposeNormalization.towerLimit` and
  `towerLimitAdditive`. The `limitFunctor` abbreviation uses the former, and
  its right-derived functor uses the latter instance.
* `def-sbc-tower-derived-evaluation-interchange` and
  `def-coef-tower-derived-evaluation-transition` own
  `Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization`'s
  `CategoryTheory.towerDerivedEvaluationInterchange` and
  `CategoryTheory.towerDerivedEvaluationTransition`. The module now directly
  publicly imports their module. Both the evaluation equation in the main theorem
  and the transition clause of `IsEvaluationComparison` use these actual maps.
* `def-sfb-abelian-tower-kinjective-resolutions` owns
  `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`'s
  `WeilConjectures.coefficientAbTowersKInjectives`. The public import supplies this
  instance for the right-derived termwise sections and abelian-tower limit.
  The former local `abelianTowerResolutions` proof is deleted, including its name
  in `lean.declarations`; nothing is reproved.
* `def-weil-strict-roos-model` owns `Sheaf.CategoryTheory.StrictRoosModel`'s
  `CategoryTheory.roosF` and `CategoryTheory.roosAugment`.

Neither `lem-sbc-unbounded-exact-adjunction-square` nor
`lem-pur-tower-limit-transpose-normalization` remains in `stmt_deps`:
the statement does not use their theorem conclusions. Their modules remain
public imports because they also contain the definition interfaces above.
Proof dependencies retain their original recorded modules, including diagram-site
realization, module K-injective resolutions, termwise homotopy adjunction,
K-injective-to-derived Hom, ringed pushforward composition, tower evaluation,
right-adjoint preservation of limits, pushforward/limit acyclicity and strict
Roos comparison. The main theorem signature is unchanged from the returned packet.

### Edge cases checked

The formulas remain typed for zero rings, zero modules and zero towers. The
identity geometric morphism gives the unit-normalized identity maps, not a free
automorphism of sections or of the limit. Constant towers and every strict
augmentation are included; no eventual constancy or surjective transition
assumption is used. All degrees are in `ℤ`, including arbitrarily negative
degrees. A restriction can fail to be invertible without violating any binder.
The evaluation equations run over all arrows `n ⟶ m`, including identities and
composites. Independent object/morphism universes in general helper definitions
are explicitly bound; no universe equality is introduced to use a narrow API.

### Searches and result

* `msearch.py ... leanfinder "Derived module global sections restriction along
  geometric morphism commutes with normalized total derived inverse limit of
  strict towers"`: eight related results, including ordinary sheaf restriction
  and `Sheaf.ΓRes_map_assoc`; none is this statement.
* `msearch.py ... loogle '"rightDerived", "limit"'`: two unrelated pointwise
  derived/colimit results; no match.
* `msearch.py ... grep 'restriction.*[Ll]imit|[Ll]imit.*restriction'
  CategoryTheory`: three small-object iteration restriction results; no match.
* `msearch.py ... leansearch "Actual derived global sections restriction
  commutes with normalized strict inverse sequence derived limit"`: ordinary
  `Sheaf.ΓRes` naturality, affine-scheme limits and inverse-system equivalences;
  no match.
* `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for restriction, sections,
  Roos/limit coherence, the item id and proposed declaration names: no exact
  duplicate. Related `RoosAdjunctionUnitCoherence`,
  `TowerLimitTransposeNormalization`, and `FlatScalarDirectImageLimitCoherence`
  have different hypotheses or comparisons; their exact interfaces were read.
* Read Mathlib's global sections, terminal sheaf, module category, derived
  K-injective and adjunction/limit APIs to reuse their constructions.

No `STATEMENT-DISPUTED` issue was found. The previous unchanged-node refusal
belonged to the stage-1 handoff; the live node still lacked a Lean record.
This delivery supplies that record and its stage-2 statement.

### Validation

`scompile.py NY lem-sfb-ringed-restriction-strict-limit-coherence
lean/Sheaf/Paper/RingedRestrictionStrictLimitCoherence.lean` compiled the final
file both under its sandbox name and its library module name against the live
published build. Both succeeded without errors or warnings other than the
expected theorem `sorry` warning. No global build or direct repository mutation
was performed.

## New nodes

All three new nodes use `existing: true` and introduce no Lean source or new choice.
The common blueprint ancestor is `det-sf-comp-coherence-cocycle`, via the item and
its inherited path. Each new node's `statement` cites exactly its `stmt_deps`.

`def-sfb-exact-ringed-module-inverse-image` records the existing `ExactMorphism`
structure and standard module/tower resolution instances. The small sites and
ring sheaves are its section variables; `ringed` gives the ringed morphism;
`coefficientIso` gives invertibility of its actual ring map; `inverse`, `additive`,
`finiteLimits`, `finiteColimits`, and `adjunction` give every other field in the
prose. `moduleResolutions` invokes the existing Grothendieck instance;
`towerResolutions` uses small module diagrams and the `AsSmall` equivalence.
Source: Stacks 08BJ, 07A7, 079P and 07A5, as documented in the published declarations.
No theorem conclusion about adjunction squares is claimed. Identity morphisms,
zero rings, and unbounded complexes remain allowed; no product-exactness
hypothesis is part of this general datum.

`def-sfb-strict-tower-limit-functor` records `towerLimit = lim` and the existing
`towerLimitAdditive` instance for an arbitrary abelian category with tower limits.
The ordinary object/map universal property in the prose is Mathlib's actual
`lim`; the instance is precisely `Functor.additive_of_preserves_binary_products`.
Source: Stacks 0940, the ordinary diagram-site direct image preceding 0941.
This is a limit of strict diagrams before deriving, with no assertion that the
limit functor is exact. Zero towers and nonsurjective transitions are included.

`def-sfb-abelian-tower-kinjective-resolutions` records the existing
`WeilConjectures.coefficientAbTowersKInjectives` instance for every universe `r`.
Its type is exactly `Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ AddCommGrpCat.{r})`.
Its value is `coefficientAbTowers_haveKInjectives`, whose published proof builds
precisely the separator from evaluation left adjoints and the pointwise AB5
structure described in the node, then invokes the standard Grothendieck construction.
Source: Injectives 079P and Sites Cohomology 0941. No boundedness restriction or
exactness of inverse limit is introduced. Zero complexes and arbitrarily negative
degrees are included.

Searches for all three ownership records (actual tool results are in
`mathlib_searches` and the launcher's `searches.jsonl`):

* `msearch.py ... leansearch "Exact coefficient preserving ringed topos morphism
  module inverse image K injective resolutions strict towers additive inverse limit
  abelian group towers"`: eight hits, including injective-resolution K-injectivity,
  sheafification finite limits and module-sheaf limits; none is this interface.
* `msearch.py ... leanfinder "ExactMorphism moduleResolutions towerResolutions
  coefficientAbTowersKInjectives towerLimit towerLimitAdditive"`: eight unrelated
  injective/projective-resolution and exactness hits; no match.
* `msearch.py ... grep
  'ExactMorphism|moduleResolutions|towerResolutions|coefficientAbTowersKInjectives|towerLimitAdditive'`:
  zero Mathlib hits.
* `rg` in the named `lean/WeilConjectures`, `lean/Sheaf` and `dag/nodes`
  directories found the exact published definitions in the three modules above.
  Their DAG references were theorem-helper records, with no definition owner.
  Upstream `moduleResolutions` belongs to scheme tensor-model interfaces and is
  not this ringed-site instance. `def-pur-tower-derived-localization-comparisons`
  already owns `cochainUnit` and is cited rather than duplicated.
* `tools/blueprint_refs.py search "exact module inverse image"` found
  `def-weil-open-closed-recollement` and `def-weil-pbc-proetale-modules`, neither
  the general interface. Searches for `"strict tower limit"` and
  `"abelian group towers"` each returned zero blueprint matches.

## Dependency modules

None. All repaired dependencies reuse their existing published definitions without
changing the dependency files or writing another module.

## Repair of returned immutable head 53acb150f1c5

H2: removed the two theorem nodes used only for plain definitions from `stmt_deps`.
Added the three definition owners above, the existing cochain-unit owner, and both
landed exact-derived evaluation definition owners. Added the direct public import
of `TowerDerivedEvaluationNormalization`. The ordinary tower-limit abbreviation
and additive instance are owned explicitly rather than attributed to the
transpose-normalization theorem. The main theorem's mathematical signature is
byte-for-byte unchanged; the natural-language statement and proof fields are unchanged.

H4: deleted the local `abelianTowerResolutions` construction and removed its
`lean.declarations` entry. Publicly imported `CoefDerivedSystemEvaluationCalculus`
and reused `WeilConjectures.coefficientAbTowersKInjectives` through the new
existing-definition node. No resolution construction was copied or reproved.

Compared the saved packet with the current read-clone item: only `lean` and
`stmt_deps` differ. The required initial saved-packet dry run passed at
`c09b3d08c1e`, but the independent return findings were still present, so this
repair changes the packet instead of merely repushing it.

## Second reading by NY

This is the dispatcher's requested self-check, performed in this worker session;
no independent worker was started. The maintainer's immutable-head reading already
accepted the mathematics, canonical-map characterizations, augmentation clause,
absence of an invertibility requirement on rho, absence of boundedness, and universes.
Re-read the repaired file and all three new records. The main signature is unchanged;
the hypothesis/clause mapping above still applies, including all derived tower
morphisms and every compatible strict augmentation. The resolution instance is
now the existing public one. Definition ownership records match the published
structure fields, ordinary `lim` abbreviation, additive instance, and abelian-tower
K-injective instance; they add no data, axioms or hypotheses to the theorem.
Neither removed theorem's conclusion occurs as a hypothesis. Both actual evaluation
maps are now cited by their own definition nodes and directly publicly imported.

The repaired module compiled in sandbox mode (18.4 s) and library mode (14.8 s)
through `scompile.py`, with no errors or warnings. Only the main theorem retains
`sorry`. No global build, direct Git command or repository write was performed.
Final dry-run and delivery results are recorded by the prescribed delivery wrapper.

The first repaired dry run requested `import_flags: []` on all three new nodes.
Added those required empty fields and split grouped definition citations into individual
`[id]` citations to clear the preflight advisories; no mathematical content changed.
