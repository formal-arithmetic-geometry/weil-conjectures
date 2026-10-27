## Worker report

The module `Sheaf.CategoryTheory.ProfiniteActionFreeRestriction` states free restriction of
set sheaves and reconstruction of the internal left action. Every theorem has proof `sorry`;
`freeRightTranslation` has its actual continuous equivariant map as data. The structure
`FreeRestriction` specifies the functor by natural section isomorphisms, the exact action
formula and its component maps. No object is selected from `freeRestriction_exists`.

Hypotheses and clauses, in node order:

- Compatible universes and small models: explicit universe `u`, with the existing
  `Base := AsSmall.{u+1} Profinite.{u}` and `Space J := AsSmall.{u+1} (ContAction Profinite J)`.
  Set sheaves and group sections take values in universe `u+1`, as in the recorded
  internal-action interface. The ULift in group sections changes no continuous map.
- The compact Hausdorff totally disconnected topological group is `(J : Type u)` with
  `[Group J] [TopologicalSpace J] [IsTopologicalGroup J] [CompactSpace J] [T2Space J]
  [TotallyDisconnectedSpace J]`. No commutativity or finiteness is assumed.
- P and P_J have precisely `baseCoverage` and `coverage J`: finite sets of covering
  arrows that are jointly surjective on the original underlying profinite spaces.
  `freeParameter` is the small-model transport of the recorded `freeAction` functor;
  it uses the original products and continuous maps. `trivialParameter` is the existing t.
- E and its internal actions are the existing `Sheaf baseCoverage.toGrothendieck` and
  `Actions J`, the latter a transparent abbreviation for `InternalActionSite.SetActions`.
  Its group is the actual continuous-map `groupPresheaf J`, with pointwise operations
  and precomposition. The contextual h_T is the ordinary continuous-map representable;
  it is not an additional conclusion of this lemma or a new definition here.
- For each F, G(F)(S)=F(H(S)) and its restrictions are the actual precomposition
  `(freeParameter J).op ⋙ F.obj`. `freeRestriction_isSheaf` states its sheaf condition.
  `FreeRestriction.sections` is a presheaf isomorphism, so it specifies both sections
  and all restriction maps at once, without silently identifying non-definitional types.
- `freeRightTranslation J S g` is the actual map `(j,s) ↦ (j*g(s),s)`, transported only
  through `AsSmall.up`. Its named well-definedness theorem supplies continuity and the
  group associativity equation used to prove equivariance; there is no data sorry.
- `FreeRestriction.action` says the original sectionwise action, evaluated with
  `InternalActionSite.setAction`, is exactly `F.obj.map (freeRightTranslation ...).op`.
  The fact that it is an internal unital associative action is part of `Actions J`.
- `freeRightTranslation_laws` spells out F(r_1)=id, F(r_g)∘F(r_h)=F(r_(gh)), and
  the displayed naturality equation for every f, g and x. Categorical `≫` is in
  left-to-right order, so its multiplication clause writes F(r_h) ≫ F(r_g).
- `FreeRestriction.functor` is a functor from sheaves on P_J to the recorded actions;
  `FreeRestriction.maps` specifies G(α)_S=α_(H(S)). Being a morphism of `Actions J`
  includes equivariance; being a functor includes identity and composition equations.
  `freeRestriction_exists` asserts existence of all these normalized data.
- `freeParameter_site` states cover preservation for every covering presieve and the
  pullback assertion for all a:A→S and b:B→S. Its `IsPullback` square uses Mathlib's
  explicit profinite fibre product and H applied to its two projections. This is
  equivalent to the displayed canonical isomorphism, including its coordinate formula:
  H's maps are `(j,x)↦(j,f(x))`, so its universal comparison is
  `(j,(a,b))↦((j,a),(j,b))`, with the displayed inverse in the node. These comparisons
  are natural by uniqueness of the pullback universal map, as explained in the docstring.

Dependency declarations read and used:

- `def-weil-size-convention`: metatheoretic convention, no Lean declaration; explicit
  universe and the already supplied `AsSmall` model implement it.
- `Sheaf.Topology.ProfiniteCondensedRing`, `Profinite.CondensedRing`, retains the
  coherent profinite site through its public imports. No coefficient ring is an input
  of this lemma; its site component is used through the shared coverage definitions.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`, `Precoverage.IsSiteForCoverings`, fixes
  the presieve site convention; the actual sites use the shared `baseCoverage`, `coverage`.
- `Sheaf.CategoryTheory.ProfiniteActionParameters`,
  `Profinite.ContinuousActionParameter.freeAction` and `trivialAction`, supply H and t.
- `Sheaf.CategoryTheory.ActionToposGeometricRestriction`,
  `InternalActionSite.SetActions` and `setAction`, supply precisely the internal-action
  category and its sectionwise action. The signatures and operation docstrings were read.
- `Sheaf.CategoryTheory.ProfiniteActionCoherentPresentation` contains `Base`,
  `parameter`, `Space`, `baseCoverage`, `coverage`, `underlying`, `groupPresheaf`,
  `group_isSheaf`, `Actions`, `freeParameter`, and `trivialParameter`. These existing
  notions are reused, not copied. This module imports it for these common definitions;
  it never uses `SetPresentation`, `coherent_generators`, or `coherent_presentation`.
- Proof dependency `WeilConjectures.CategoryTheory.SiteContinuousPushforwardSheaf`,
  `CategoryTheory.siteContinuous_pushforward_isSheaf`, is imported privately; its
  full signature and proof were read. The docstring also gives the direct matching-family
  proof, avoiding any assumption of closure under arbitrary indexed composition.
- Proof dependency `lem-sfb-profinite-action-finite-cover-site` currently has no `lean`
  record. Its relevant continuous-map descent assertion is already exposed as
  `group_isSheaf` above. No unstated site construction is needed for this statement.

Import constraint for the maintainer: the broader coherent-presentation node has this
item as a proof dependency, while its module already owns the common site definitions
needed here. Under stages/2-statements.md §3(7), do not automatically add the reverse
proof import into `ProfiniteActionCoherentPresentation.lean`: it would close an import
cycle. No DAG edge to that downstream theorem has been added. A future separation of
its common definitions into a foundational module can remove this existing ownership
constraint; this delivery does not alter another node's module.

Edge cases checked: empty profinite parameters; the empty covering of the empty target;
the trivial group; noncommutative J (the order r_h∘r_g=r_(gh) is essential); arbitrary
parameter maps and nonconstant g; identity and composite sheaf maps. Groups are nonempty,
so no illicit empty-group case occurs. The covering assertion uses actual presieve
finiteness, and includes empty and repeated-index family presentations through their
presieves. The pullback assertion is for all maps, not just covering arrows.

Searches performed:

- `msearch.py leanfinder`: "Restrict a sheaf on profinite continuous group actions along
  the free action functor J times S and recover an internal action by right translations".
  Eight hits: `ContAction.resComp`, condensed constructors, and ordinary continuous-action
  restriction. None states this reconstruction; `ContAction.resComp` changes the group.
- `msearch.py loogle`: `"Condensed", "Action"`; zero hits.
- `msearch.py grep` in `Condensed`: `right.*[Tt]ranslation|[Ff]ree.*[Aa]ction|[Aa]ction.*[Ss]heaf`;
  zero hits.
- `rg -n 'free-restriction|freeRestriction|rightTranslation'` in both `lean/WeilConjectures`
  and `lean/Sheaf`: unrelated free-module restriction and ordinary cochain translations;
  the broader coherent presentation discusses right translations in its proof docstring
  but supplies no normalized free-restriction functor or separate theorem asserting it.
- The exact node-id search in `lean/WeilConjectures` has no match. The existing shared
  definitions were checked by reading their complete source declarations, including
  the recorded parameter functor and internal-action signatures.

Source read: `literature/blueprint/latest/blueprint/sec-six-functors-basics/`
`sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3).
As the node records, this is agent-formulated auxiliary infrastructure, not an extra
claim asserted in that paragraph. The supplied five-step auxiliary proof is carried
through the theorem docstrings. No statement correction and no disputed statement.

Validation: `scompile.py Q20 lem-sfb-profinite-action-free-restriction` compiled the
module successfully in both sandbox and library module modes, with no warnings or errors.


## New nodes

`def-sfb-profinite-action-space-site` records the five existing plain definitions
`Space`, `underlying`, `coverage`, `trivialParameter`, and `freeParameter` in
`Sheaf.CategoryTheory.ProfiniteActionCoherentPresentation`, with `existing: true`.
No Lean module or declaration is added or changed for this node. Its statement uses
`def-sfb-profinite-action-base-coefficients` for `Base` and `parameter`, and
`def-sfb-profinite-action-parameters` for the actual trivial/free action functors.
The item now cites both the new definition node and the landed base-coefficients node,
which owns its `Base`, `baseCoverage`, `groupPresheaf`, and `Actions` interfaces.
This repairs the sole H2 return at immutable head `7041473dc2e7`; the downstream
coherent-presentation theorem is not cited as a statement dependency.

The new definition statement matches the existing declarations as follows:

- J's seven typeclass hypotheses are the original compact Hausdorff totally
  disconnected topological-group hypotheses, with explicitly declared universe u.
- The small action category is exactly `Space := AsSmall.{u + 1}
  (ContAction Profinite.{u} J)`, retaining all continuous actions and equivariant maps.
- The underlying-space functor is `AsSmall.down` followed by `forget₂`.
- The coverage is precisely `W.uncurry.Finite` and pointwise joint surjectivity using
  `(underlying J).map f`; it includes the empty presieve on the empty space.
- Both parameter functors are the canonical composites `AsSmall.down` followed by
  the recorded trivial/free action functor followed by `AsSmall.up`. Consequently
  their original spaces, actions, and maps are those displayed in the node.

Fresh repair searches (2026-10-24), with the raw service results stored in the node:
`msearch.py leansearch` for "Small model of profinite spaces with continuous group
 action finite jointly surjective covering presieves and free trivial parameter functors"
returned eight profinite-group/category results, none this combined site construction;
`msearch.py loogle` for `"ContAction", "AsSmall"` returned zero hits;
`msearch.py grep` for `freeParameter|trivialParameter|def coverage|def underlying`
in Mathlib `CategoryTheory/Action` returned zero hits. The upstream
`WeilConjectures/CategoryTheory` search returned no corresponding declarations.
The project source contains exactly the reused five declarations at lines
105, 110, 116, 125, 131 of `ProfiniteActionCoherentPresentation.lean`.
The definition-node DAG search found no owner of these five declarations;
`blueprint_refs.py search 'profinite action'` found zero blueprint nodes, and
`blueprint_refs.py ancestor` returned None, recorded as JSON null.
The latest blueprint direct-images paragraph (3) was reread: these remain honestly
identified as auxiliary agent-formulated infrastructure, not a statement of that paragraph.

## Second reading by Q20

I reread the saved node statement and every declaration of the retained module.
The group hypotheses and the small-site/set universes are unchanged. The definition
owners are now explicit: base-coefficients for the base site and internal actions,
parameters for the original t and H, and the new space-site node for the transported
category, coverage, underlying functor, and t/H. These are plain constructions before
any coherent-presentation theorem; the new node has no proof dependencies.

`freeRestriction_isSheaf` supplies the sheaf clause for the exact precomposition
`H.op ⋙ F.obj`. `freeRightTranslation` supplies the actual `(j,s) ↦ (j*g(s),s)` map.
`freeRightTranslation_laws` gives unit, multiplication in contravariant left-action
order `F(r_h) ≫ F(r_g) = F(r_(gh))`, and naturality for every continuous parameter map.
`FreeRestriction.sections`, `.action`, and `.maps` fix respectively all sections and
restriction maps, the displayed original action, and each original sheaf-map component;
its `.functor` supplies equivariance and functoriality. `freeParameter_site` supplies
both covering preservation and the actual pullback square for every pair of maps;
the canonical comparison and its inverse have the stated coordinates. The represented
h_T is contextual notation and adds no extra conclusion to formalize.

Empty spaces and their empty covers, the trivial group, non-abelian groups, nonconstant
g, arbitrary pullback maps, and identity/composite sheaf maps remain included. No
hypothesis, theorem statement, proof, or Lean byte was changed in this repair. The
item JSON changes only `lean` and allowed additions to `stmt_deps`; the current-main
comparison before repair differed only in `lean`. The one new JSON has the exact
stage-2 definition-node fields and an existing declaration signature copied verbatim.
The stage-3 import-cycle advisory is retained: shared definitions can be extracted
into a foundational module later, without adding a reverse import now.

Repair validation: the unchanged Lean module compiled cleanly in sandbox and library
modes (13.4 s and 7.5 s). The repaired dry run required `import_flags` on the new
definition node; added the empty list as required by the server preflight schema.
