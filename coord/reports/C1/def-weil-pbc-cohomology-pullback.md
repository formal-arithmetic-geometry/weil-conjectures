## Worker report

The module `Sheaf.AlgebraicGeometry.CohomologyPullback` defines
`AlgebraicGeometry.Etale.cohomologyPullback`.  For a morphism of schemes
`u : X ⟶ Y`, an étale abelian sheaf `G` on `Y`, and `q : ℕ`, it is the additive
map from `Sheaf.H G q` to the cohomology of the inverse image sheaf.  Its body
uses the established `AlgebraicGeometry.Etale.cohomologyMap`; the docstring
records the node's K-injective-resolution recipe and the resolution-independence
identification.

Hypothesis and clause correspondence:

- `u : X ⟶ Y` is the morphism of schemes from `def-pc-scheme`.
- `G : Sheaf Y.smallEtaleTopology AddCommGrpCat` is an abelian sheaf on the
  small étale site (`def-weil-pbc-etale-site` and
  `def-weil-pbc-abelian-etale-sheaves`).
- `q : ℕ` is the nonnegative cohomological degree.
- The codomain `Sheaf.H (((u)^*[AddCommGrpCat]).obj G) q` is the cohomology of
  the inverse image sheaf, and the body `cohomologyMap u G q` is the induced
  pullback map.  The K-injective choices and the unit-on-sections construction
  are the resolution presentation described in the node and source.

Dependency declarations read and used include `AlgebraicGeometry.Scheme`,
`AlgebraicGeometry.Scheme.smallEtaleTopology`, `CategoryTheory.Sheaf`,
`AlgebraicGeometry.Etale.upperStar`, `CochainComplex.IsKInjectiveResolution`,
`CochainComplex.etale_kinjective_resolutions_exist`,
`AlgebraicGeometry.Etale.upperStar_abelian_exact`,
`AlgebraicGeometry.Etale.cohomology`, `DerivedCategory`,
`CategoryTheory.Functor.mapDerivedCategoryPlus`, and
`CochainComplex.IsKInjective.nonempty_homology_iso`.

Edge cases checked: `q = 0` is allowed; arbitrary schemes and morphisms are
allowed; no properness, separatedness, étaleness, or nonzero condition is added;
the inverse-image sheaf is taken on the small étale site of `X`.

Searches: LeanFinder/LeanSearch for pullback maps on étale or sheaf cohomology
found only sheaf-level pullbacks and no resolution-level map; Loogle for
`CategoryTheory.Sheaf.H` found only fixed-site sheaf functoriality; grep and
`rg` over Mathlib, `WeilConjectures`, and `lean/Sheaf` found the existing
`AlgebraicGeometry.Etale.cohomologyMap` (Ext presentation) but no declaration
of this K-injective-resolution notion.  The source declaration was therefore
not recorded as `existing`.

## Earlier second reading (a previous round; superseded)

Reading the node and module together, `u`, `G`, and `q` match exactly, and the
codomain applies inverse image to `G` before taking degree-`q` cohomology.  The
module introduces no extra hypotheses and permits degree zero and arbitrary
scheme morphisms.  The implementation uses the existing Ext realization of the
same pullback map; the module docstring explicitly ties it to the node's
K-injective resolution construction and cited independence statement.  No
mismatch was found.

## Second reading by C1

I read the complete node (including its derived-complex clause), its dependency
records and their declarations, and the source text at
`/home/ubuntu/c1-stacks-review/cohomology.tex`, Section `section-functoriality`,
Lemma `lemma-functoriality`, equations `equation-functorial-derived` and
`equation-functorial`, and Remark `remark-explain-arrow` (01F7--01FB).
I also read `sites-cohomology.tex`, Remark `remark-before-Leray` (08J6), and
`etale-cohomology.tex`, Section `section-functoriality` (04I0). These source
places require a general morphism, not a proper or étale morphism; the complexes
in the derived-complex formulation have bounded-below representatives. The
node specializes the general f-map to the inverse-image adjunction unit.
No correction of the node's statement is needed or made.

The worker's report and the earlier second reading are superseded where they
claim that the delivered Ext-map alias realizes the resolution definition.
The dependency `def-weil-pbc-etale-cohomology` explicitly records the distinction
between `Sheaf.H` and cohomology of derived global sections, with their comparison
a stage-3 bridge. A docstring alone cannot supply that bridge. The original file
also omitted the derived-complex clause altogether.

Object, hypothesis, and conclusion checklist, in the order of the node:

1. Schemes X,Y and a morphism u:Y→X: `Scheme.{u}` and `f : X ⟶ Y`, with source
   and target names exchanged consistently. PASS. The Scheme and Scheme.Hom
   signatures in pinned Mathlib/Scheme.lean introduce no extra geometric condition.
2. Small étale sites and an abelian sheaf on the target:
   `Sheaf Y.smallEtaleTopology AddCommGrpCat.{u+1}`. PASS. I opened the topology
   definition in Mathlib/Sites/Etale.lean and the full-subcategory definition
   `CategoryTheory.Sheaf` in Mathlib/Sites/Sheaf.lean. These are precisely the
   dependency declarations, with the project's coefficient universe convention.
3. Direct image, sections of direct image, and inverse image with unit:
   `upperStarLowerStarAdjunction ... f` and its `.unit`, followed by the existing
   `lowerStarCompGlobalSectionsIso ... f`. PASS after repair. I opened `lowerStar`,
   `upperStar`, and the adjunction in UpperLowerStar/Defs.lean, and the sections
   isomorphism in UpperLowerStar/GlobalSections.lean. The latter evaluates at the
   terminal objects and identifies their base change, so realizes Γ(Y,f_*F)=Γ(X,F).
4. Choose G[0]→I K-injective: `s : (HomologicalComplex.single _ (.up ℤ) 0).obj G ⟶ I`
   and `_hs : QuasiIso s ∧ I.IsKInjective`. PASS after repair. I read the dependency
   module KInjectiveResolutions.lean: its named abbreviation for module sheaves
   is exactly this conjunction of the existing Mathlib predicates. For abelian
   sheaves we use those same predicates directly, not a new private predicate
   or a forced change of coefficients to module sheaves.
5. Resolve termwise inverse image by J:
   `r : ((upperStar ... f).mapHomologicalComplex (.up ℤ)).obj I ⟶ J` and
   `_hr : QuasiIso r ∧ J.IsKInjective`. PASS after repair. The dependency
   KInjectiveResolutionsExist.lean states existence, comparison up to homotopy,
   and K-injectivity of bounded-below injective complexes. Existence is not an
   additional hypothesis here: the chosen resolutions are arguments, as in the node.
6. Exact inverse image and hence a resolution of f⁻¹G:
   the functor is the dependency's `upperStar`; I read `upperStar_abelian_exact`
   in EtaleInverseImageExact.lean and the existing exactness instances. PASS.
   No exactness premise is added. The composite resolution is not new chosen
   data: it is inverse image of s followed by r, as the docstring explains.
7. Nonnegative q and the two resolution-computed groups:
   `(q : ℕ)` and homology at `(q : ℤ)` of Γ(Y,I) and Γ(X,J). PASS after repair.
   Γ is the existing `Sheaf.Γ`, the functor underlying the dependency's
   `rightDerivedGlobalSections` in Derived/LowerShriek.lean, which I opened
   together with `cohomology`. The original `Sheaf.H` endpoints were an H3 fault.
8. The actual section map Γ(Y,I)→Γ(X,f⁻¹I)→Γ(X,J):
   `cohomologyPullbackComplex` applies `NatTrans.mapHomologicalComplex` to
   the unit whiskered by Γ and the existing direct-image/sections isomorphism,
   then composes with the termwise Γ-image of r. PASS after repair. The unitors
   and associator only align composite functors. In degree n this is exactly
   Γ(unit at Iⁿ), the terminal-object identification, and Γ(rⁿ).
   The first worker's `cohomologyMap f G q` body did not express this construction.
9. Map induced in cohomology: `cohomologyPullback` is
   `(HomologicalComplex.homologyFunctor ... (q : ℤ)).map
   (cohomologyPullbackComplex f I J r)`. PASS after repair. A morphism of
   `AddCommGrpCat` objects is the requested additive group map.
10. Bounded-below representative K and its resolution: `derivedCohomologyPullback`
    takes `K`, `_hK : ∃ n : ℤ, K.IsStrictlyGE n`, s:K→I with the same resolution
    conjunction, and the same r and J. PASS after repair. Inverse image is the
    termwise functor, consistent with the dependency `mapDerivedCategoryPlus`
    read in DerivedCategory/ExactFunctor.lean. There is no bound imposed on the
    chosen I or J; arbitrary K-injective resolutions are allowed.
11. The class in D⁺(Ab): `DerivedCategory.Q.map` of the SAME complex map, with
    endpoints QΓ(Y,I), QΓ(X,J). PASS after repair. I read the localization Q in
    Mathlib/DerivedCategory/Basic.lean and the dependency DerivedCategories.lean.
    We express the morphism in ambient D(Ab); D⁺ is a full subcategory, so its Hom
    is this very Hom. The endpoints represent derived global sections of the
    bounded-below input and its exact inverse image, hence belong to D⁺.
    This avoids adding arbitrary membership witnesses or strict bounds on I,J.
12. Resolution dependence and later independence, naturality, composition,
    restriction, and alternative derived-unit description: resolutions are explicit
    arguments. PASS. None of those separate results is assumed or proved here.
    I opened the dependency `CochainComplex.IsKInjective.nonempty_homology_iso`:
    it compares homology after an additive functor for K-injective resolutions.
    We do not silently use it to identify the Ext map with the resolution map.

Edge cases: q=0 is included. The zero sheaf and zero complexes are allowed.
Empty schemes are allowed; neither `Nonempty` nor a field/characteristic
hypothesis occurs. There is no family index or nonempty-index restriction.
K may have any integer lower bound, including a negative bound. I,J may be
unbounded as complexes. The universe u is bound, schemes share the usual
scheme universe, and coefficient groups live in u+1 as in the dependency/site
encoding; this places no finite-dimensional or small-coefficient restriction.
No variables or universes are unbound (also checked by compilation).

Independent searches (other wording than the original worker):

- LeanFinder through msearch.py: `global sections map induced by inverse image
  of sheaves derived functor`: eight hits, only sheaf pushforward, sheaf Hom,
  and Γ section maps; no resolution-level cohomology map.
- Loogle through msearch.py: `"rightDerivedGlobalSections"`: zero hits.
- LeanSearch through msearch.py: `morphism on cohomology from global sections
  of a K-injective resolution and inverse image`: service returned Internal
  Server Error, recorded UNAVAILABLE, with no mathematical verdict. The other
  kinds and source grep were used as required by the search fallback.
- rg in pinned Mathlib's SheafCohomology, all upstream WeilConjectures, project
  lean/Sheaf, and dag/lean_names_upstream.json: `cohomologyMap`,
  `globalSectionsUpperStarMap`, `rightDerivedGlobalSections`, and
  `cohomologyPullbackComplex|derivedCohomologyPullback`. Found the Ext-based
  `Etale.cohomologyMap` in UpperLowerStar/TopologicalInvariance.lean, which I
  opened and checked, and the degree-zero unit-on-sections construction and
  direct-image/sections iso in UpperLowerStar/GlobalSections.lean. Reused the
  adjunction and sections iso. Derived/GlobalSections.lean explicitly leaves
  the general derived pullback transformation as a TODO; its existing
  pullback invariance iso applies only to scheme isomorphisms. No existing
  declaration realizes the node's resolution map and derived class. Therefore
  the repaired module is needed, rather than an `existing: true` record.

Repairs: replaced the Ext alias and its endpoints; retained the correct module
path and main declaration name; added the resolution-complex map and derived
class; made all chosen resolutions explicit; added the standard header and
source docstrings; updated lean.statement verbatim through stage2_delivery.py
and listed all three declarations. The node itself, dependencies, and their
statements are unchanged. No new notion/node or dependency module is needed.
All definition bodies are concrete existing categorical operations; there are
no sorries or new theorems in this delivery. The node has no proof steps, as it
is a definition. The docstrings spell out its construction in order.

Validation: scompile.py compiled the complete repaired module on the server
in 4.5 seconds with exit code 0 and no warnings. Imports supply the actual
adjunction/sections iso and the derived-global-sections infrastructure
(including additivity and the chosen derived category instances). All lines
are at most 100 characters. Delivery dry-run/preflight and final delivery follow.
