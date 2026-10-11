## Worker report

The module `Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit` states
`AlgebraicGeometry.Scheme.exists_affineEtaleSite_colimit`. Its sole theorem has proof
`by sorry`; it defines no new notion. The item's node changes only in `lean`.

The source was read directly at
[Stacks 0EYL](https://stacks.math.columbia.edu/tag/0EYL), especially the first paragraph
of its proof, since the repository's literature checkout does not contain the TeX file.
The qcqs restriction is already explicit in the node; it is not a new hypothesis.
The comments on that page also identify the need for strictification of pullback functors.

Hypotheses and objects:

- Directed set: `{I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]`.
  The index lives in the scheme carrier universe, as the project requires.
- Inverse system of schemes: `D : Iᵒᵖ ⥤ Scheme.{u}`. Its functor laws give the
  inverse-system identity and composition laws. For `h : i ≤ j`, the transition from
  `X_j` to `X_i` is `D.map (homOfLE h).op`.
- Affine transitions: `[∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]`.
- Every stage quasi-compact: `[∀ i : Iᵒᵖ, CompactSpace (D.obj i)]`.
- Every stage quasi-separated: `[∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]`.
- Limit and projections: `c : Cone D`, `hc : IsLimit c`; `X` is `c.pt` and
  `f_i` is `c.π.app (op i)`. No affineness of projections is assumed; it follows from
  the limit-affine-transition dependency.
- Affine étale sites are precisely the recorded `FullAffineEtale`,
  `fullAffineEtalePrecoverage`, and `fullAffineEtaleTopology`, not the spectrum-only
  `AffineEtale` category. Standard covers include finite jointly surjective families.

Clause (1), base change and its coherent strictification:

- `U i j h` is `u_{ji}`, and `v i` is `u_i`. They are existentially chosen, normalized
  by `U i i le_rfl = 𝟭 _`, rather than independently assumed as hypotheses.
- The natural first projections `p i j h` and `q i` are transformations between
  the underlying-scheme functors. Their `IsPullback` clauses specify exactly the
  scheme fibre products with the indicated transitions and limit projections.
  The second projections are the affine étale objects' structure maps.
  Thus these are actual base change functors, not arbitrary functors with descent
  properties. Naturality of `p` and `q` specifies their action on morphisms by the
  pullback universal property. Objects of the target full subcategories are affine
  and étale, so well-definedness is included.
- Cover preservation is `R ∈ fullAffineEtalePrecoverage ... → R.map U ∈ ...`, and
  the analogous clause for `v`. `PreservesLimit (cospan f g) U` and its `v` analogue
  state pullback preservation. These are the two Stacks continuity conditions.
  All such pullbacks are preserved because the functors are base change; this also
  includes the covering-arrow pullbacks used by the site's continuity definition.
- The existential `IsContinuous` instances use Mathlib's continuous-functor notion.
  Each functor additionally has a left adjoint `L` to the recorded
  `sheafPushforwardContinuous (Type u)` and `PreservesFiniteLimits L`.
  This is exactly the definition of a morphism of sites: its inverse image is the
  finite-limit-preserving left adjoint of restriction. Stating the adjunction avoids
  choosing a second implementation of inverse image; uniqueness of left adjoints
  identifies it with the recorded `sheafPullback` when using that implementation.
  Finite-colimit preservation is automatic for a left adjoint.
- `gamma : U i j h ⋙ U j k h' ≅ U i k (h.trans h')` and
  `delta : U i j h ⋙ v j ≅ v i` render the canonical composition comparisons.
  Their underlying scheme maps commute with the first projections in the displayed
  projection equations. Since they are morphisms over the final base, they also
  commute with the second projections. The pullback universal property makes these
  the canonical comparisons, not arbitrary isomorphisms.
- The two normalized `HEq gamma (Iso.refl ...)` clauses and normalized `delta`
  clause implement the identity-index conventions. The four-index equation is the
  gamma cocycle and the three-index equation is the compatible delta cocycle.
- `F : I ⥤ Cat.{u, u+1}` gives the strictly functorial sites `C_i`; identity and
  composition equalities hold by its functor laws. `Q i` is their precoverage, with
  all four recorded site-axiom instances and `Finite R.uncurry` for covers.
- Each `e i` is an equivalence preserving and reflecting covers, explicitly by
  `R ∈ fullAffineEtalePrecoverage ... ↔ R.map (e i) ∈ Q i ...`.
- `theta` renders `e_i ⋙ u'_{ji} ≅ u_{ji} ⋙ e_j`, using Lean's diagrammatic
  composition order. `eta` renders `e_i ⋙ v'_i ≅ v_i`.
  `F.map ... ⋙ v' j = v' i` is strict cone compatibility; the `Arrow.mk` equation
  matches theta and eta with the original delta comparison, including endpoints.
- The strict transitions preserve covers and pullbacks, are continuous, and have
  finite-limit-preserving left adjoints on sheaves. The `v'` functors are continuous
  morphisms of sites too. This follows equally by transport across `e` and `eta`.

Clause (2): `∀ A : c.pt.FullAffineEtale, ∃ i Ai, Nonempty ((v i).obj Ai ≅ A)`.
The isomorphism is inside the full affine étale category, hence is over `X`.

Clause (3), descent of morphisms: for any `f : (v i).obj A ⟶ (v i).obj B`, the
existential `j`, `h : i ≤ j`, and `g : (U i j h).obj A ⟶ (U i j h).obj B` satisfy
`f = delta.inv.app A ≫ (v j).map g ≫ delta.hom.app B`. This is precisely base change
of the descended morphism with canonical comparison isomorphisms. Eventual equality
is the next clause: `(v i).map f = (v i).map g → ∃ j h, U.map f = U.map g`.

Clause (4): the finite-family biconditional has arbitrary `n`, target `A`, sources
`B : Fin n → ...`, and arrows `f`. It is a cover iff there are a stage cover `fi`,
a target isomorphism `t`, and source isomorphisms `s` with
`v.map (fi a) ≫ t.hom = (s a).hom ≫ f a`. This records the entire family, including
repetitions, and not merely a refinement or an unrelated covering sieve.
Every finite indexing set is bijective to some `Fin n`; the node's reindexing
convention and standard-cover definition make this equivalent to its finite-family form.

Clause (5): `K : Cocone F`, with `IsColimit (Cat.objects.mapCocone K)` and
`IsColimit (Cat.arrows.mapCocone K)`, is exactly the recorded category-colimit encoding.
`K.ι.app i ⋙ W = v' i` specifies the induced comparison `W`.
`P` is the colimit precoverage, explicitly the union of images of stage coverings
(the `h ▸ Ri.map ... = R` equality includes its target). Its four site-axiom instances
assert it is a site. Finally `W.IsEquivalence` and
`R ∈ P A ↔ R.map W ∈ fullAffineEtalePrecoverage c.pt (W.obj A)` give equivalence of
categories and preservation and reflection of coverings, exactly as sites.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `IsAffineHom` (the affine-morphism
  dependency is Mathlib, so its `mathlib_match` is the declaration record).
- Scheme conventions have no separate definition; the actual stage properties are
  `CompactSpace` and `QuasiSeparatedSpace`.
- `Sheaf.AlgebraicGeometry.LimitAffineTransition`:
  `AlgebraicGeometry.exists_limit_affine_transition`, read with its complete
  signature and proof docstring; it supplies the projection-affineness step.
- `Sheaf.AlgebraicGeometry.FullAffineEtaleTopos`:
  `Scheme.fullAffineEtaleInclusion_special_equivalences` and its docstring;
  `Sheaf.AlgebraicGeometry.FullAffineEtaleSite`: `FullAffineEtale`,
  `fullAffineEtaleInclusion`, `fullAffineEtalePrecoverage`, `fullAffineEtaleTopology`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its
  projections and universal property. The statement uses the equivalent existing
  `CategoryTheory.IsPullback` square API to specify normalized choices of base change.
- Sites-and-cohomology dependency: the recorded `Precoverage` site-axiom classes,
  `toGrothendieck`, `Sheaf`, `Functor.IsContinuous`, `sheafPushforwardContinuous`.
  The cohomology declarations `Sheaf.H'` and `cohomologyPresheafFunctor` were read,
  but this node has no cohomology clause.
- `Sheaf.CategoryTheory.SiteSystemStrictification`:
  `CategoryTheory.exists_site_system_strictification`, full signature and docstring.
- `Sheaf.CategoryTheory.ColimitSites`: `CategoryTheory.exists_colimit_site`, full
  signature and proof docstring; `Cat.objects` and `Cat.arrows` give its colimit encoding.

The last two abstract theorems bundle small categories at one universe. The concrete
full affine sites have object universe `u+1` and Hom universe `u`, so the statement
uses `Cat.{u,u+1}`. Their same abstract notions are used, without duplicating either
notion. In stage 3 the abstract results may be applied to universe-lifted categories
and index, or their universe parameters generalized. No smaller-universe restriction
is imposed on the schemes or on their affine étale objects here.

Edge cases checked before writing:

- `Nonempty I` is part of the source's directed-set convention. No empty inverse
  system, which would instead have a terminal scheme as its limit, is silently included.
- A one-stage system has identity base change, reflexive gamma and delta, and the
  original site as its colimit.
- Empty schemes and empty affine étale objects are allowed. `Fin 0` explicitly
  covers the empty-cover case; the joint-surjectivity clause is vacuous precisely
  for an empty target. If the limit is empty, qcqs compactness permits eventual
  descent of this empty covering to an empty stage object.
- Repeated arrows in a finite covering are allowed by the explicit family formulation.
- No field, characteristic, Noetherian, separatedness of the stages, or affine-stage
  assumption is added. The only geometric restrictions are the node's qcqs and affine
  transitions. Arbitrary affine étale objects, not just affine opens, are quantified over.
- The scheme and index carrier universes agree; full sites retain all their objects
  in `Type (u+1)` with Hom universe `u`. Universes and all binders are explicit.

Searches for an existing declaration:

- `msearch.py ... leanfinder`: "The small affine etale site of an inverse limit of
  qcqs schemes with affine transition maps is the filtered colimit of their affine
  etale sites". Eight hits: `Scheme.exists_isAffine_of_isLimit`,
  `nonempty_isColimit_Γ_mapCocone`, affine-limit helpers, and `Scheme.etaleTopology`.
  None states the colimit of affine étale sites or all five node clauses.
- `msearch.py ... loogle`: `Scheme.FullAffineEtale, IsColimit, Scheme.Etale.pullback`.
  Zero hits; unknown identifier `Scheme.FullAffineEtale` in the search index.
- `msearch.py ... grep`: `0EYL|colimit.*[Aa]ffine.*[Ee]tale|[Aa]ffine.*[Ee]tale.*colimit`
  in Mathlib AlgebraicGeometry. Zero hits.
- `rg` in `WeilConjectures`, matching affine étale and 0EYL, found pro-affine étale
  site machinery and comparisons, not this statement. Search for the exact node id
  in the source library had no hits. No upstream name record for this node was found.
- `rg` in `lean/Sheaf` found the full affine étale site and topos modules and three
  proof-docstring references to this node (EtaleSetSectionContinuity,
  ConstructibleEtaleModuleLimitDescent, EtaleCohomologyLimitOfSchemes), but no declaration.
  The new full declaration name was checked against the existing source and Mathlib
  searches; the delivery preflight also checks for name collisions.

No statement dispute, correction, new definition node, or dependency replacement was
needed. The module compiled locally with no errors or warnings (2.4 seconds).

## Second reading by K1

I independently read the base node and sandbox module, all nine statement-dependency
nodes, and the declarations in FullAffineEtaleSite, FullAffineEtaleTopos,
LimitAffineTransition, SiteSystemStrictification and ColimitSites. I read the Mathlib
signatures of Scheme, IsAffineHom, pullback, IsPullback and
sheafPushforwardContinuous. No new nodes or dependency modules are in this delivery.
The sandbox has no statement correction.

The local literature tree lacks the cited TeX, so I fetched the Stacks source files
into the sandbox scratchpad and read etale-cohomology.tex lines 7336--7404
(lemma-colimit-affine-sites) and sites.tex lines 3770--3856
(situation-inverse-limit-sites and lemma-colimit-sites). These match
[0EYL](https://stacks.math.columbia.edu/tag/0EYL),
[0A34](https://stacks.math.columbia.edu/tag/0A34), and
[09YL](https://stacks.math.columbia.edu/tag/09YL). The first proof paragraph of 0EYL
is the node's explicit qcqs case; the limit's qcqs property follows from affine
projections. Neither the source nor the node requires Noetherian schemes, affine
stages, a field, or a characteristic restriction. The source's strict-composition
issue is already explicitly addressed in this node by its strictification clause.

My object/hypothesis/conclusion checklist, with the Lean rendering and verdict:

1. Nonempty directed preordered set I: `{I : Type u} [Preorder I] [Nonempty I]
   [IsDirected I (· ≤ ·)]`. Matches the directed-set convention spelled out in the
   strictification dependency; antisymmetry is not needed. PASS.
2. Inverse system of schemes with its identity and composition laws:
   `D : Iᵒᵖ ⥤ Scheme.{u}`. The transition X_j to X_i is
   `D.map (homOfLE h).op` for `h : i ≤ j`. PASS.
3. Every transition affine: `[∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]`.
   The recorded Mathlib class says the inverse image of each affine open is affine.
   PASS.
4. Each stage quasi-compact and quasi-separated: the two dependent instances
   `CompactSpace (D.obj i)` and `QuasiSeparatedSpace (D.obj i)`. These are the
   scheme properties, without strengthening to separatedness or Noetherianity. PASS.
5. Limit X and all projections f_i: `c : Cone D`, `hc : IsLimit c`, with X = `c.pt`
   and f_i = `c.π.app (op i)`. This quantifies over any limiting cone; no arbitrary
   nonlimiting X is allowed and no additional geometric condition on X is assumed.
   PASS.
6. Full small affine étale categories and standard coverings: `FullAffineEtale`,
   `fullAffineEtaleInclusion`, `fullAffineEtalePrecoverage`,
   `fullAffineEtaleTopology`. I checked that the category is the full subcategory
   of the small étale category on objects with affine domain, and the precoverage
   is finite jointly surjective étale families. It is not the spectrum-only
   Mathlib presentation. PASS.
7. Clause (1), actual base change: existential `U`, `v`, `p`, `q` and their
   `IsPullback` squares. The first projection is p or q; the second is the
   structure map of the resulting étale object. Naturality and the over-category
   morphisms specify the induced map on fibre products. Membership in the target
   FullAffineEtale category already includes affineness and étaleness. Normalized
   identities are `U i i le_rfl = 𝟭 _`. PASS.
8. Clause (1), continuous morphisms of sites: cover-image implications, pullback
   preservation, and existential `IsContinuous` instances for U and v. For each,
   the existential L is left adjoint to the recorded
   `sheafPushforwardContinuous (Type u)` and satisfies `PreservesFiniteLimits L`.
   A left adjoint preserves finite colimits; uniqueness of left adjoints identifies
   L with the dependency's sheaf inverse image. Thus neither exactness nor the
   direction of the site morphism is lost. All-pullback preservation here follows
   from base change, rather than introducing a new input hypothesis. PASS.
9. Clause (1), canonical comparisons and coherence: `gamma`, `delta`, their
   equations with p and q, normalized HEq identity clauses, and the four-index
   gamma and three-index delta equations. Commutation with the first projection
   plus being over the final base characterizes the canonical fibre-product
   comparison, so these cannot be unrelated natural isomorphisms. PASS.
10. Clause (1), strictification: `F : I ⥤ Cat.{u, u+1}`, precoverages Q with all
    four site-axiom instances and finite covers, equivalences e preserving and
    reflecting covers, theta and eta comparisons, and strict
    `F.map ... ⋙ v' j = v' i`. Functor laws give strict transition identities and
    composition; the Arrow equation includes endpoints and relates the comparisons
    to delta. The strict transitions and cone functors are continuous and have
    finite-limit-preserving inverse images. PASS.
11. Clause (2), descent of every object: `∀ A : c.pt.FullAffineEtale, ∃ i Ai,
    Nonempty ((v i).obj Ai ≅ A)`. Isomorphisms in this category are over X. PASS.
12. Clause (3), descent of every map: binders i, A, B, f precede j, h, g; the
    equation is `f = delta.inv.app A ≫ (v j).map g ≫ delta.hom.app B`.
    The directions of both comparison components give exactly the source and
    target of f. PASS.
13. Clause (3), eventual equality: `(v i).map f = (v i).map g → ∃ j h,
    (U i j h).map f = (U i j h).map g`. This is a common later stage, not equality
    at the initial stage or a statement only about existence of lifts. PASS.
14. Clause (4), all standard covering families: the `∀ n A B f` biconditional
    uses `Presieve.ofArrows`, with a common stage, target isomorphism t, source
    isomorphisms s, and one commuting equation for every `a : Fin n`.
    It descends the whole given family, not just a covering refinement or a sieve.
    Fin n represents every finite indexing set up to the dependency's permitted
    bijective reindexing. Repetitions are retained by B, f, s and the component
    equations even though the precoverage uses a presieve. PASS.
15. Clause (5), category colimit and induced functor: `K : Cocone F`, the two
    `IsColimit` assertions for `Cat.objects.mapCocone K` and
    `Cat.arrows.mapCocone K`, and `K.ι.app i ⋙ W = v' i` (with toFunctor).
    This is the recorded object-and-arrow set-colimit encoding, not an arbitrary
    category equivalent to X's site without the specified cocone. PASS.
16. Clause (5), precisely the colimit coverings and site equivalence: P is
    characterized by `Ri ∈ Q i Ai ∧ h ▸ Ri.map ... = R`; its four site-axiom
    instances make it a site. `W.IsEquivalence` together with
    `R ∈ P A ↔ R.map W ∈ fullAffineEtalePrecoverage c.pt (W.obj A)` is the
    required equivalence preserving and reflecting coverings. PASS.

Edge cases: empty I is outside the source's directed-set convention, explicitly
excluded by Nonempty. A singleton index permits identity functors and reflexive
comparisons. Empty schemes and empty affine étale objects are allowed; `n = 0`
in clause (4) includes the empty covering precisely for an empty target. There are
no nonzero-ring, field or characteristic assumptions. All binders and universes
are explicit: I and schemes use u, full sites have object universe u+1 and Hom
universe u, and Cat retains those levels. The existing abstract strictification
and colimit-site theorems use Cat.{u,u}; they can be used after universe lifting
with Type (u+1) sheaves and restriction to smaller-valued sheaves. This is a
stage-3 application issue, not a restricted site in this statement or a missing
notion. No hollow hypothesis or definition appears.

Independent existence searches (different wording from the worker):

- LeanFinder: "Descent of finite covering families and morphisms in the affine
  etale category under cofiltered scheme limits". Eight hits, including
  exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType and
  exists_isAffineOpen_preimage_eq. These are individual limit results, not this
  site-colimit theorem.
- Loogle: `IsColimit, AlgebraicGeometry.Scheme`; no hits, with IsColimit unknown
  in that service's index. This search is inconclusive on its own.
- msearch grep: `colimit.*[Ee]tale|[Ee]tale.*colimit|0EYL`, no hits.
- Direct rg with the same concept and the proposed declaration name across
  Mathlib AlgebraicGeometry, WeilConjectures and lean/Sheaf. The hits are ring
  colimits, cohomology or section continuity, étale gluing, and docstring uses of
  this node. No existing declaration states these five clauses. The exact
  declaration name has no collision.

No semantic mismatch was found and nothing in the Lean statement or node was
rewritten. The second reading adds this report section and the independent source
and search evidence. The module has one named theorem with `by sorry`, no data
with sorry, no auxiliary proof, no private notion or file-local notation, and no
line over 100 characters. Its source docstring follows all eight node proof steps.
Local lcompile succeeded in 2.4 seconds without errors or warnings. The delivery
script checks signature equality and performs the final server compilation.
