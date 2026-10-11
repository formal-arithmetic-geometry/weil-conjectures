## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleSetInverseImageRestriction` states
`AlgebraicGeometry.etaleSetInverseImageRestriction`; its only proof is `sorry`.
The node is unchanged except for its `lean` record. No new notions, dependency
modules, or statement corrections were needed.

Hypotheses and clauses:

- Schemes and the étale morphism `j : U → X` are `{X U : Scheme.{u}}`,
  `(j : U ⟶ X)`, and `[Etale j]`. No separation, finiteness, or nonemptiness
  condition is imposed.
- Small étale site objects are `X.Etale` and `U.Etale`, with the recorded
  `Scheme.smallEtaleTopology`. Set sheaves are
  `Sheaf X.smallEtaleTopology (Type (u + 1))`, the same coefficient universe as
  the recorded inverse-image/composition dependency.
- The node's functor sending `V → U` to `V → U → X` is
  `MorphismProperty.Over.map ⊤ (inferInstance : Etale j)`.
  The existing `Etale.localizationRestriction (Type (u + 1)) j inferInstance`
  is precomposition with its opposite, on objects and morphisms. Its result is
  already bundled as a sheaf on `U.smallEtaleTopology`, so the sheaf assertion
  of clause (1) is included in its type, without a new definition or a hypothesis
  that presupposes an unproved property. Continuity is proved in the source.
- The inverse image is `Scheme.etaleSetPullback j`, exactly the functor used in
  `etaleSetInverseImageCompositionUnits`. The existential `ρ` is an isomorphism
  of functors from set sheaves on `X` to set sheaves on `U`; therefore its sheaf
  components `ρ.app G` are isomorphisms, natural in `G`. This is clause (1).
- For clause (2), the quantified `W : X.Etale` and
  `s : G.obj.obj (op W)` range over every site object and every section.
  `MorphismProperty.Over.pullback @Etale ⊤ j` sends `W` to `W ×_X U` over `U`.
  The left side applies `(ρ.hom.app G).hom.app` at that object to the section
  given by the unit of `sheafAdjunctionContinuous`, exactly the unit used by
  the dependency declaration, with all its local notations expanded.
  The right side is `G.obj.map` on the opposite of the counit of
  `MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j inferInstance trivial`.
  Reading the definition shows this counit is `Over.homMk (pullback.fst _ _)`
  with its structural commutativity proof. Thus it is exactly restriction along
  `W ×_X U → W`, not an arbitrary comparison map. `trivial` proves the membership
  of `j` in the top morphism property, required by the site adjunction's API;
  it adds no assumption or conjunct to the node.
- The last 'in particular' is included in `ρ`: evaluate its sheaf isomorphism
  at the identity étale object `U → U`. The target of that component is
  definitionally `G` evaluated at `U → X`, by the restriction formula above.
  It is an isomorphism of sets `(j⁻¹G)(U) ≅ G(U)`. No extra choice of a global
  sections comparison is necessary, and it is the same component of `ρ`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`;
  the full affine-local definition and its docstring were read.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`
  and `Scheme.Etale`, and the covering-family characterization.
- `Mathlib.CategoryTheory.Sites.Sheaf`: `CategoryTheory.Sheaf`, the full
  subcategory for `Presheaf.IsSheaf`. This is the usable `mathlib_match` of
  `def-weil-pbc-etale-sheaf-of-sets`, which has no `lean` record.
- `Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits`:
  `etaleSetInverseImageCompositionUnits`; the whole signature and docstring
  were read. Its imported `Scheme.etaleSetPullback` definition was also read
  in `Sheaf.AlgebraicGeometry.EtaleSheaves`. The module uses that functor and
  the exact same adjunction unit, rather than a second inverse image.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback` and `pullback.fst`, used through the
  recorded site pullback and its counit. Their full signatures were read.
- Additional existing API:
  `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `Etale.localizationRestriction`, whose full definition and section/map
  equations were read; `Mathlib.CategoryTheory.MorphismProperty.OverAdjunction`:
  `Over.pullback` and `Over.mapPullbackAdj`, including the counit definition.
  Despite its module's name, `localizationRestriction` accepts every étale
  morphism, not merely an open immersion. Its definition does not require
  abelian coefficients; this was confirmed by the successful Type-valued compile.

Source checks: the local Stacks tex is absent on this machine, so read the source
at https://stacks.math.columbia.edu/tag/03S2 (paragraph after Definition 59.70.1)
and https://stacks.math.columbia.edu/tag/00XZ. Tag 03S2 explicitly describes
restriction through `U_et → X_et`, also for sheaves of sets. The theorem docstring
carries all five DAG proof steps and their named dependencies.

Edge cases checked mathematically before writing: `j = id` gives the canonical
identity comparison with its projection unit; empty `U` and empty site objects
are allowed and restriction remains a sheaf (the empty covering forces singleton
sections on the empty object). A general étale `j` can have multiple sheets and
need not be a monomorphism: no `[Mono j]` or open-immersion assumption was used.
Arbitrary schemes and characteristics are allowed. Universes are explicitly
bound and use the coefficient universe already fixed by the dependency.
No statement disputes were found.

Searches made (2026-10-11, via `/home/ubuntu/weil-launcher/msearch.py`):

- leansearch: 'inverse image of sheaves of sets along an etale morphism equals
  restriction and the adjunction unit restricts sections along the pullback
  projection'. Service unavailable: Internal Server Error; no search verdict.
- leanfinder: 'inverse image sheaves of sets along etale morphism is restriction
  with unit given by projection'. Eight results about restriction to open subsets
  in ringed spaces and schemes; none is this small-étale set-sheaf statement.
- loogle: 'Functor.sheafPullback, MorphismProperty.Over.map'. Zero hits,
  unknown identifier `Functor.sheafPullback`.
- grep Mathlib/CategoryTheory: 'sheafPullback|sheafPushforwardContinuous|def map|
  mapPullbackAdj'. Twenty-five returned hits largely concern unrelated map
  definitions; direct `rg` and reading `MorphismProperty/OverAdjunction.lean`
  located the needed adjunction and counit, not this theorem.
- `rg -n 'etaleSetPullback|etale.*[Rr]estrict|sheaf.*[Rr]estrict|
  inverseImage.*[Rr]estrict'` in `WeilConjectures` and `lean/Sheaf` found the
  recorded inverse image and general localization restriction. Direct reading
  of the generic and étale localization modules found existing natural comparison
  isomorphisms for a differently named generic pullback, but no single declaration
  with this recorded inverse image and the node's explicit section/unit equation.
- `grep -rn 'lem-weil-pbc-sets-etale-inverse-image-restriction'` in
  `WeilConjectures`: no hits. Searching `dag/lean_names_upstream.json` for the
  new theorem name and `localizationRestriction` returned no hits.

Validation: server `scompile.py` compiled the final module in 1.9 seconds with
exit code 0 and no warnings. No local build was run.


## Second reading by G1

Read the repository node, the delivered node and Lean module independently, then
all five statement-dependency nodes and their declaration signatures. Verdict:
no mathematical or Lean-statement mismatch; retain the module and node unchanged.
No new definition nodes, dependency modules, or statement correction are present.

Object/hypothesis/conclusion checklist (the node's statement in order):

1. Schemes X and U and an étale morphism j : U → X: rendered by
   `{X U : Scheme.{u}} (j : U ⟶ X) [Etale j]`. Exact. Read the affine-local
   `Etale` class in Mathlib/AlgebraicGeometry/Morphisms/Etale.lean and the
   dependency's equivalence to flat, locally finitely presented, unramified.
2. The small étale sites, and V → U viewed as V → X: `X.Etale`, `U.Etale`
   and `smallEtaleTopology` use the recorded Mathlib site. Read its category
   definition `MorphismProperty.Over @Etale ⊤ X` and its jointly-surjective
   covering characterization. Composition is `Over.map ⊤ (inferInstance : Etale j)`;
   its occurrence is inside the existing restriction definition. Exact.
3. G is a sheaf of sets on X, with restriction maps: the universal binder
   `G : Sheaf X.smallEtaleTopology (Type (u + 1))` uses the dependency's
   full-subcategory `CategoryTheory.Sheaf`; its underlying functor is `G.obj`.
   Read Sheaf.lean:302 and the set-valued sheaf condition, rather than treating
   G as an abelian sheaf. Exact, with the same universe as the recorded inverse image.
4. G|U has value G(V → X), with G's maps: the target functor of ρ is
   `Etale.localizationRestriction (Type (u + 1)) j inferInstance`. Read its
   definition and object/morphism equations in the upstream OpenImmersion/Defs
   module: precomposition with `(Over.map ⊤ h).op`, bundled as a sheaf by the
   existing continuity instance. Despite the path, this definition needs only
   `Etale j`, not `Mono j`, an open immersion, or abelian coefficients. Exact.
5. The inverse image j⁻¹G and the unit section j*s: `Scheme.etaleSetPullback j`
   is precisely the dependency's inverse image. Read EtaleSheaves.lean:63–69:
   left Kan extension followed by sheafification along `Over.pullback @Etale ⊤ j`.
   Read the entire CompositionUnits theorem; the explicit
   `sheafAdjunctionContinuous ... .unit.app G` in this module expands its η.
   No independent or arbitrary unit was introduced. Exact.
6. Clause (1), restriction is a sheaf and ρG is an isomorphism natural in G:
   `∃ ρ : Scheme.etaleSetPullback j ≅ Etale.localizationRestriction ...`
   is an isomorphism of functors between the stated sheaf categories. Thus the
   target already proves the sheaf condition, and `ρ.app G` is a sheaf iso
   natural in G. This existential occurs before `∀ G`, as required for one
   natural comparison, and imposes no additional hypothesis. Exact.
7. Clause (2), every W in X_et and every s in G(W): the universal binders
   `(W : X.Etale) (s : G.obj.obj (op W))` have exactly this range. The equality's
   left side evaluates `(ρ.hom.app G).hom.app` at `Over.pullback ... .obj W`,
   on the section furnished by the unit. The right side is `G.obj.map` of the
   opposite of `Over.mapPullbackAdj ... .counit.app W`. Read OverAdjunction.lean:
   the pullback object's structure map is `pullback.snd W.hom j`, and this
   counit is `Over.homMk (pullback.fst W.hom j) pullback.condition ...`.
   It is exactly restriction along W ×X U → W, using the dependency's chosen
   fibre product and its first projection. The proof `trivial` concerns only
   membership in ⊤, not a mathematical assumption. Exact, including variance.
8. In particular, ρG(U) : (j⁻¹G)(U) ≅ G(U): evaluate `ρ.app G` at the identity
   étale object `Over.mk ⊤ (𝟙 U) inferInstance`. Under `Over.map`, its structural
   morphism is `(𝟙 U) ≫ j = j`, so the target is G evaluated at U → X. This
   follows from the same functor iso and adds no independent clause or choice.
   Exact; an additional existential would only repeat the component already given.

Source: local literature contains neither Stacks tex file. Fetched the primary
Stacks repository's etale-cohomology.tex and sites.tex into this item's scratchpad
and read section-extension-by-zero, Definition definition-extension-zero and its
following description, and section-localize with definition-localize and the
following restriction formula. Also checked the rendered tags
https://stacks.math.columbia.edu/tag/03S2 and
https://stacks.math.columbia.edu/tag/00XZ. The former assumes only étale j here;
separatedness and finiteness appear in later statements, not this one. The latter
assumes an arbitrary site and its object U. No extra global source hypotheses
are missing.

Edge cases: empty U, empty X (hence empty U), and empty W are included. The empty
cover forces the expected singleton sections of a sheaf on an empty object;
no nonempty assumption appears. Identity j gives the usual identity-compatible
comparison. A many-sheeted étale map is included, with no Mono requirement.
Terminal sheaves and sheaves with empty section sets are included; there is no
additive zero object in the set-sheaf category. There is no index set, n, or
characteristic hypothesis in the statement. The arbitrary bound universe u and
Type (u+1) agree with the dependency's coefficient universe; larger set sizes
can be accommodated by increasing u and lifting the scheme/site. All variables
and universes in the delivered signature are explicitly bound.

Independent duplicate searches, using different terms from the worker:

- LeanSearch via msearch.py: 'sheaves of types on a slice site restriction is the
  left adjoint of base change precomposition': unavailable, Internal Server
  Error; no negative verdict inferred.
- LeanFinder via msearch.py: 'localization of a site sheaves pullback adjunction
  projection counit': eight generic sheaf pullback, sheafification comparison,
  and module pullback declarations. None states this small-étale set-sheaf
  comparison with the projection/unit equation.
- Loogle via msearch.py: 'Adjunction.leftAdjointUniq': zero hits, identifier
  unknown to that service. Direct rg found and read the actual generic API in
  Mathlib/CategoryTheory/Adjunction/Unique.lean, including the unit equation.
- Direct rg over Mathlib sites and adjunctions and WeilConjectures/SixFunctors/
  Etale for `mapPullbackAdj`, `localizationRestriction`, and `leftAdjointUniq`:
  existing restriction and generic uniqueness API, not the entire statement.
  Read `Etale.upperStarIsoLocalizationRestriction` and its source upperStar
  definitions: these carry Grothendieck abelian coefficient hypotheses and
  cannot serve as an existing declaration for this set-valued node.
- Direct rg over WeilConjectures, repository lean/Sheaf and
  dag/lean_names_upstream.json for the new declaration, node id, and
  restriction/unit combinations: no existing exact declaration. Related
  ringed-space and abelian-sheaf statements concern different categories.

Conventions and H5/H6/H8/H9: no new definitions (hence no hollow data), one named
statement with `by sorry`, no proved helper, no file-local notation or instance,
no unbound implicit. Both imports supply definitions used by the signature.
Module/declaration docstrings name the source and blueprint id, and reproduce
all five DAG proof steps with the relevant dependencies. Lines are at most 100
characters. Checked the node's lean.statement against the source text before
`:=`: verbatim equal, including whitespace.

Changes: appended this independent reading only; no Lean or node repair needed.

Second-reader validation: scompile.py compiled the unchanged delivered module
on the server in 1.9 seconds, exit code 0, with no warnings or errors.
