## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes` states
`AlgebraicGeometry.Etale.nonempty_isColimit_etale_cohomology_of_isLimit` and
`AlgebraicGeometry.Etale.nonempty_isColimit_etale_cohomology_spec_ring_colimit`.
Both proofs are `sorry`. No definitions or auxiliary proofs are introduced, and the node
is unchanged except for `lean`.

Sources read: [Stacks 09YQ](https://stacks.math.columbia.edu/tag/09YQ) and
[Stacks 01YW](https://stacks.math.columbia.edu/tag/01YW). The local literature checkout
is absent on this machine, so these source pages were opened directly. The general
statement matches 09YQ; 01YW supplies the ring-limit clause.

Hypothesis and clause correspondence for the general theorem:

- Directed index: `I : Type u`, `[Preorder I]`, `[IsDirected I (· ≤ ·)]`, `[Nonempty I]`.
  The nonempty binder is the usual nonemptiness of a directed indexing set. Using a preorder
  rather than a partial order follows the current directed-set convention. Its universe is
  the scheme universe, as required by the standing brief.
- The inverse system of schemes and its transition maps are `D : Iᵒᵖ ⥤ Scheme.{u}` and
  `D.map f.op`, for `f : i ⟶ j` (i ≤ j). The functor supplies their identity/composition laws.
- Each stage is quasi-compact and quasi-separated: the `CompactSpace (D.obj i)` and
  `QuasiSeparatedSpace (D.obj i)` instance binders.
- All transition morphisms are affine: the `IsAffineHom (D.map f)` instance binder.
- The scheme limit and projections are `c : Cone D`, `hc : IsLimit c`, and `c.π.app (op i)`.
- The abelian sheaves at the stages are the dependent family `F` of
  `Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u+1}`.
- The sheaf transition maps are `φ f`, with source the recorded `upperStar` applied to `F i`.
  `hidentity` uses `D.map_id` and `upperStarId`; `hcomposition` uses `D.map_comp` and
  `upperStarComp`, so this is precisely a system of sheaves, including its coherence laws.
- The diagram of pulled-back sheaves on the limit is `G`. The isomorphisms `eG i` identify
  its objects with `f_i^{-1} F_i`. The equation `hG` fixes every transition map as the
  composition isomorphism followed by the pulled-back `φ`, conjugated by these isomorphisms.
  Thus `G` is a presentation of the prescribed diagram, not an arbitrary replacement.
- The colimit sheaf is `L.pt`, with coprojections `L.ι.app i` and `hL : IsColimit L`.
- Nonnegative cohomological degree is `p : ℕ`, including p = 0.
- The cohomology diagram is `H`. `eH i` identifies its objects with `Sheaf.H (F i) p`,
  and `hH` fixes its arrows as `cohomologyMap (D.map f.op)` followed by `Sheaf.H.map (φ f)`.
- The comparison cocone is `B`. `eB` identifies its target with `Sheaf.H L.pt p`, while
  `hB` specifies its legs: cohomology pullback along the projection, then the map induced
  by the sheaf coprojection. The `eG i` inverse only transports from the prescribed
  pulled-back object to its chosen diagram presentation.
- The conclusion `Nonempty (IsColimit B)` says precisely that these legs exhibit the target
  as the colimit of the cohomology groups. Equivalently the canonical induced map from any
  chosen colimit is an isomorphism; it is not a claim about an unspecified isomorphism.
  The object isomorphisms and cocone equations are presentation data, not extra geometric
  hypotheses: the canonical diagrams and cocones supply such data by functoriality.

Hypothesis and clause correspondence for the ring case:

- `I` has the same directed-set binders; `R : I ⥤ CommRingCat.{u}` is the directed ring
  system. `c : Cocone R` and `hc : IsColimit c` express its ring colimit C, including the
  coprojections `c.ι.app i`.
- The compatible maps to a scheme `T` are `v i : Spec (R.obj i) ⟶ T`, with the equations
  `wv i j f : v j = Spec.map (R.map f) ≫ v i`.
- The map on the limit is `vLimit : Spec c.pt ⟶ T`, with the equations `wLimit i` specifying
  its composites with every projection `Spec.map (c.ι.app i)`.
- The abelian sheaf is `G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u+1}`.
- `p : ℕ` covers all nonnegative degrees. `H` and `eH` present the groups
  `H^p(Spec C_i, v_i^{-1} G)`; `hH` fixes the transition maps as pullback along
  `Spec.map (R.map f)`, followed by `Sheaf.H.map` of the inverse of `upperStarComp`.
  Its inverse is the direction from iterated inverse image to `(v j)^{-1} G`.
- `B`, `eB`, and `hB` present the comparison to `H^p(Spec C, vLimit^{-1} G)` with exactly
  the same pullback/composition recipe along the ring-colimit coprojections.
- The first conclusion is `Nonempty (IsLimit (Scheme.Spec.mapCone c.op))`, which asserts
  `Spec C = lim Spec C_i` with those projections, up to the categorical universal property.
- The second conclusion quantifies over every arrow and asserts
  `IsAffineHom (Spec.map (R.map f))`, retaining the affine-transition clause explicitly.
- The third conclusion `Nonempty (IsColimit B)` is the stated canonical cohomology
  isomorphism for pullbacks of the single sheaf G.

Dependencies used (source declarations and their full signatures/docstrings were inspected):

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` in `Mathlib.AlgebraicGeometry.Scheme`, and
  its category morphisms; also `Spec` and `Spec.map` for the ring clause.
- `def-weil-pbc-scheme-conventions`: a convention-only node, with no declaration to import.
  We use the stated Mathlib notions `CompactSpace`, `QuasiSeparatedSpace`, and `IsAffineHom`
  from the geometry/topology modules imported by `Mathlib.AlgebraicGeometry.AffineTransitionLimit`.
- `def-weil-pbc-abelian-etale-sheaves`: `CategoryTheory.Sheaf` and
  `AlgebraicGeometry.Scheme.smallEtaleTopology` from `Mathlib.CategoryTheory.Sites.Sheaf`
  and `Mathlib.AlgebraicGeometry.Sites.Etale`.
- `def-weil-pbc-inverse-image`: `AlgebraicGeometry.Etale.upperStar`, with its identity and
  composition isomorphisms `upperStarId` and `upperStarComp`, in
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` / `.Coherence`.
- `def-weil-pbc-etale-cohomology` and `def-weil-pbc-cohomology-pullback`: we use the accepted
  paired abelian-sheaf encoding `CategoryTheory.Sheaf.H`, `CategoryTheory.Sheaf.H.map`,
  and `AlgebraicGeometry.Etale.cohomologyMap`, as the records explicitly prescribe for
  abelian-sheaf PBC citers. `cohomologyMap` is imported from
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`.
  The record for cohomology also names `Etale.cohomology` and `rightDerivedGlobalSections`
  in `.Derived.LowerShriek`; their definitions/docstrings were read. As the records say,
  the natural bridge between `Sheaf.H`/its Ext pullback and K-injective cohomology/its
  unit pullback belongs to stage 3; this delivery introduces no second encoding.

Edge cases checked before writing: p = 0 is included; zero sheaves and empty schemes are
allowed; the zero ring is allowed in the affine clause. No torsion, characteristic,
Noetherian, separated, nonempty-scheme, or nonzero-ring assumption is added. The index is
nonempty by the directed-system convention, but no particular index is selected. A singleton
index reduces to the usual identity comparison. All cohomology and sheaf universes use the
established `u+1` encoding, with indices and schemes/rings in `u`. The transition and
coprojection directions were checked, especially the inverse composition isomorphism in
the ring case.

Searches:

- `msearch.py ... leansearch "Etale cohomology commutes with inverse limits of quasi compact
  quasi separated schemes with affine transition maps"`: service unavailable, Internal
  Server Error; recorded as unavailable, no verdict inferred.
- `msearch.py ... leanfinder "etale cohomology of inverse limit of quasi compact quasi
  separated schemes with affine transition maps is colimit of cohomology"`: eight results,
  including `nonempty_isColimit_Γ_mapCocone`, `exists_appTop_π_eq_of_isLimit`, and section
  descent/equality lemmas from `AffineTransitionLimit`. These concern structure-sheaf
  sections, not abelian etale sheaf cohomology; none states this node.
- `msearch.py ... loogle "CategoryTheory.Sheaf.H, CategoryTheory.Limits.IsColimit"`:
  successful search, zero results.
- `msearch.py ... grep "cohomology.*[Ll]imit|H_map_isColimit|09YQ" AlgebraicGeometry`:
  zero Mathlib results. Direct inspection of Mathlib `SheafCohomology.Basic` located
  `Sheaf.H`, `Sheaf.H.map` and `Sheaf.functorH`, but no varying-site continuity theorem.
- `rg` over the entire upstream `WeilConjectures` tree for the item id and
  `H_map_isColimit|cohomology.*limit` found the fixed-scheme theorem
  `Scheme.H_map_isColimit_of_isFiltered` in `AlgebraicGeometry/Curve/Reductions.lean`
  and `AlgebraicGeometry/Sites/CohomologyContinuity.lean`. The latter file was read whole:
  its theorem `isZero_rightDerived_sectionsFunctor_upperStar_of_isLimit` states only
  vanishing when every stage vanishes, for pullbacks of one sheaf. Neither is this theorem.
- `rg` over project `lean/Sheaf` found `EtaleCohomologyFilteredColimit.lean` (fixed scheme),
  `EtaleComplexCohomologyLimit.lean` (uniformly bounded-below complex systems, with supplied
  derived-unit pullback data), and `LimitPullbackSectionsColimit.lean` (degree-zero module
  sections on a descended affine etale object). Those files were read and are distinct.
- `tools/lean_names_upstream.py show` was consulted for this id; no attachment was listed.
  A name search in `dag/lean_names_upstream.json`, the upstream source and `lean/Sheaf`
  found neither new theorem name already declared.

Validation: the complete module compiled on the server with `scompile.py J1
lem-weil-pbc-etale-cohomology-limit-of-schemes <module>`, exit code 0 in 6.8 seconds,
with no warnings. The only change needed after the initial compile was replacing an
infinity-symbol variable suffix with the ordinary identifiers `vLimit` and `wLimit`.
No statement correction, dependency module, new node, or disputed statement is needed.

## Second reading by J1

I read the sandbox node, the complete module, each of its six statement dependency
records and the source declarations, independently of the worker's correspondence.
I also read the actual Stacks TeX from the primary stacks/stacks-project repository:
`etale-cohomology.tex`, `definition-inverse-system-sheaves` and `theorem-colimit`
(Tag 09YQ), with their surrounding paragraphs; `limits.tex`,
`lemma-directed-inverse-system-affine-schemes-has-limit` (01YW), the section introduction
and next lemma; and `categories.tex`, `definition-directed-set`.
The local literature checkout is absent. The primary tag pages were also checked:
https://stacks.math.columbia.edu/tag/09YQ and https://stacks.math.columbia.edu/tag/01YW.
There are no ambient Noetherian, torsion, characteristic or separation hypotheses.
Stacks explicitly defines a directed set as a nonempty preordered set with upper bounds,
so the preorder and nonemptiness in the module reproduce the source convention exactly.

My object/hypothesis/conclusion checklist, with the corresponding Lean and verdict:

1. A directed indexing set I: `{I : Type u} [Preorder I]
   [IsDirected I (· ≤ ·)] [Nonempty I]` in both declarations. Exact: reflexivity and
   transitivity come from Preorder, common upper bounds from IsDirected, nonemptiness
   from Nonempty. Antisymmetry is not required by the source.
2. Schemes X_i and compatible inverse-system transition morphisms:
   `D : Iᵒᵖ ⥤ Scheme.{u}`, `D.obj (op i)`, `D.map f.op` for `f : i ⟶ j`.
   Exact: these maps go X_j → X_i; functor laws give the inverse-system laws.
3. All stages quasi-compact and quasi-separated:
   `[∀ i : Iᵒᵖ, CompactSpace (D.obj i)]` and
   `[∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]`. Exact scheme-topological properties;
   neither separated nor Noetherian is imposed.
4. Every transition morphism affine:
   `[∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]`. Exact, including identities.
   This is a genuine restriction on arbitrary transitions, not merely on identities.
5. The limit X with its projections f_i: `c : Cone D`, `hc : IsLimit c`,
   `c.pt`, `c.π.app (op i)`. Exact categorical limit; cone naturality supplies
   f_i = f_j followed by f_ji. No affine hypothesis on X is added.
6. Abelian sheaves F_i on each small etale site:
   `F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1}`.
   Exact; these are arbitrary abelian sheaves, not only torsion or module sheaves.
7. A system of transition maps f_ji inverse-image F_i → F_j:
   `φ f` with source `(upperStar _ (D.map f.op)).obj (F i)` and target `F j`.
   Exact. `hidentity` and `hcomposition` spell out the unit and cocycle laws with
   the actual upstream identity/composition isomorphisms. I read `upperStarComp`:
   its hom goes from composite pullback to iterated pullback, so the hom in
   `hcomposition`, rather than its inverse, is correct.
8. The directed diagram of pulled-back sheaves on X:
   `G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}`, `eG`, `hG`.
   Exact presentation: eG identifies its objects with f_i inverse-image F_i;
   hG specifies its arrows as the composite-pullback isomorphism followed by
   f_j inverse-image of φ_ji, conjugated by eG. These presentation binders allow
   arbitrary choices of isomorphic diagram objects without changing the notion.
9. F = colim f_i inverse-image F_i and its coprojections:
   `L : Cocone G`, `hL : IsColimit L`, `L.pt`, `L.ι.app i`. Exact; this is the
   prescribed colimit of the prescribed diagram, not an arbitrary sheaf.
10. All nonnegative cohomological degrees: `p : ℕ`. Exact, including zero.
11. The directed system H^p(X_i,F_i) with pullback then φ:
   `H`, `eH i : H.obj i ≅ AddCommGrpCat.of (Sheaf.H (F i) p)`, `hH`.
   Exact: `cohomologyMap (D.map f.op) (F i) p` pulls back the class and
   `Sheaf.H.map (φ f) p` applies the sheaf transition. No arbitrary comparison
   map is substituted for this transition.
12. The canonical comparison to H^p(X,F): `B : Cocone H`, `eB`, `hB`.
   Exact: hB fixes its leg as cohomology pullback along f_i followed by the map
   of the sheaf coprojection. `(eG i).inv ≫ L.ι.app i` has source the actual
   pulled-back sheaf; eB transports its target to the actual cohomology group.
13. That comparison is an isomorphism: `Nonempty (IsColimit B)`. Exact universal
   property: the prescribed cocone is colimiting, equivalently its induced map
   from any colimit of H is invertible. This asserts the canonical comparison,
   not existence of some unrelated group isomorphism. Presentation data exist
   by the inverse-image and cohomology functoriality cited by proof step 1.
14. A directed ring system C_i with colimit C:
   `R : I ⥤ CommRingCat.{u}`, `c : Cocone R`, `hc : IsColimit c` in the second
   theorem. Exact arbitrary commutative rings, not fields or nonzero rings.
15. A scheme T and abelian sheaf G on T_et: `T : Scheme.{u}`,
   `G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}`. Exact, no condition on T.
16. Compatible maps v_i and their limit v:
   `v i : Spec (R.obj i) ⟶ T`, `wv i j f : v j = Spec.map (R.map f) ≫ v i`,
   `vLimit : Spec c.pt ⟶ T`, `wLimit i`. Exact directions and compatibility;
   no scheme-over-T structure has been silently substituted for these maps.
17. Spec C is the scheme limit with the given projections:
   first conjunct `Nonempty (IsLimit (Scheme.Spec.mapCone c.op))`. Exact:
   this cone has vertex Spec c.pt and projections Spec.map of c.ι.app i.
18. Affine transition morphisms in the ring case: second conjunct
   `∀ (i j : I) (f : i ⟶ j), IsAffineHom (Spec.map (R.map f))`. Exact and explicit.
19. Ring-case canonical cohomology isomorphism for all p:
   eH presents H^p(Spec C_i,v_i inverse-image G), eB presents
   H^p(Spec C,vLimit inverse-image G), hH and hB fix the canonical maps,
   and the third conjunct is `Nonempty (IsColimit B)`. Exact. In this case
   `upperStarComp ... .inv.app G` must go from iterated pullback to the
   pullback along v_j or vLimit; I checked that direction against its signature.

Dependency reading: Scheme and Scheme.Hom in Mathlib's Scheme.lean are schemes as
locally ringed spaces locally isomorphic to affine spectra and their morphisms.
IsAffineHom in Morphisms/Affine.lean is inverse images of affine opens being affine.
The conventions node has no declaration to import. Mathlib Sites/Etale.lean defines
smallEtaleTopology on schemes etale over T. Sites/Sheaf.lean defines Sheaf as the full
subcategory of presheaves satisfying the sheaf condition. Upstream UpperLowerStar/Defs.lean
constructs upperStar by presheaf left Kan extension and sheafification and provides its
adjunction; Coherence.lean supplies the identity coherence used here. The abelian
cohomology and pullback records explicitly permit the paired Sheaf.H/cohomologyMap encoding:
I read SheafCohomology/Basic.lean (Ext from constant ULift Z, H.map),
TopologicalInvariance.lean (cohomologyMap is H.mapFunctor of the exact upperStar), and
Derived/LowerShriek.lean (rightDerivedGlobalSections and cohomology). Their K-injective/Ext
comparison is the recorded stage-3 bridge, not a new notion required in this delivery.
All declarations used have the right domain and codomain and their coefficient instances
are available for AddCommGrpCat.{u+1} without new hypothesis binders. No dependency module
or new definition node is present or needed. There is no statement_change and no correction.

Edge cases: empty index sets are excluded by the source's definition of directed set,
not by an added assumption. Singleton and non-antisymmetric directed preorders are covered.
The empty scheme is allowed at every stage and at T; zero sheaves are allowed; the zero
ring is allowed in CommRingCat and yields the empty spectrum. Degree zero is included.
There is no characteristic, invertibility, finiteness, torsion or nonzero restriction.
I is in the scheme/ring universe u, as required by the project; for any particular small
system and coefficient family one may enlarge u, so the common universe imposes no
cardinality bound. No separate smaller test-object universe or unbound universe occurs.

Independent searches (different wording from the worker):

- `msearch.py ... leanfinder "continuity of abelian sheaf cohomology under inverse systems
  of schemes"`: eight hits. `continuousCohomology` concerns topological groups;
  `Sheaf.cohomologyPresheaf` is a definition on one site; the AffineTransitionLimit
  hits concern structure-sheaf sections. No match.
- `msearch.py ... loogle '"cohomology", "isLimit"'`: successful, zero hits.
- Direct rg of upstream WeilConjectures, project lean/Sheaf and Mathlib/AlgebraicGeometry
  for `09YQ|cohomology.*(limit|continuity)|isColimit.*(cohomology|Sheaf.H)` found the nearby
  declarations. I opened the whole upstream Sites/CohomologyContinuity.lean and project
  EtaleCohomologyContinuity.lean. The upstream theorem concludes vanishing assuming
  stage vanishing for pullbacks of one sheaf; the project theorem has a torsion hypothesis
  and a sheaf descending to one stage. Neither states this arbitrary system of arbitrary
  abelian sheaves. Fixed-scheme filtered-colimit and complex-system results likewise have
  different objects. Thus H4 does not require dropping this module. The worker's
  LeanSearch outage remains recorded honestly in the Worker report.

Mismatch and repair: I found no mathematical signature mismatch. The step-6 docstring
mentioned exactness of filtered colimits without naming its DAG dependency. I added
`lem-weil-pbc-filtered-colimit-abelian-groups-exact` beside that fact, retaining the
correct proof text and both signatures. Steps 1–8 still follow the node's general-case
proof and the second theorem's docstring gives step 9. All three docstrings have the
source place and blueprint id. There are exactly two theorem proofs, both `sorry`,
no definitions, no private/local notions and no file-local notation or instances.
All lines satisfy the 100-character bound. Every universe and variable is explicitly
bound. The node's lean.statement is verbatim the primary theorem signature, verified
by text extraction; the second declaration is listed in lean.declarations.

Validation: independent scompile of the module succeeded, exit 0, 6.9 seconds, with
no warnings. The delivery dry run and final delivery below recompile the final module
including the docstring citation repair and check the current server base.
