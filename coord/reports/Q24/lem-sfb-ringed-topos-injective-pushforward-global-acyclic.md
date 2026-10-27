# Stage-1 worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-ringed-topos-injective-pushforward-global-acyclic.json`: item split, statement unchanged, five proof steps; Mathlib no exact match.
- `citations.json`: ten citations, each quoting the cited statement verbatim.
- `searches.jsonl`: actual search-command results, retained as evidence.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. No Lean files, compiler, Lake or build tools were used. Writes are confined to this item sandbox.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id and for injective pushforward, ringed topoi and acyclicity. `AlgebraicGeometry.Scheme.Modules.module_pushforward_injective_acyclic` in `WeilConjectures/AlgebraicGeometry/ModulePushforwardInjectiveAcyclic.lean:59` concerns scheme/Zariski modules and cannot supply arbitrary ringed topoi. Topological abelian pushforward results likewise have different objects. The existing generic presentation and site-evaluation results are in `lean/Sheaf/`, with existing DAG nodes, and are reused as those nodes rather than offered as an exact project attachment for this item.

## WANTED

None: the necessary Stacks sources are present.

## Changes and source route

The imported item had no proof. Its statement is correct, including arbitrary geometric morphisms and absence of flatness; no statement dispute or correction is needed. The tempting assertion that module direct image preserves injectives without flatness is not used. I read `sites-cohomology.tex`, Tag 072Z (`lemma-direct-image-injective-sheaf`) and Tag 0731 (`lemma-limp-acyclic`), including their proofs. I retain their reduction to a continuous site presentation, reuse the already reviewed object-evaluation acyclicity theorem, specialize to the terminal object of the replacement site, and write the original-presentation resolution comparison explicitly.

The existing DAG search found `lem-weil-pbc-ringed-topos-site-presentation` for Tag 03CR and `lem-weil-pbc-ringed-presentation-transport` for exact equivalence of module categories. The already reviewed `lem-weil-pbc-ringed-site-direct-image-injective-evaluation-acyclic` states precisely the continuous-site case required here, with no flatness. Its full statement and proof were read; the coefficient category is modules, not just abelian sheaves. The separate `lem-weil-pbc-injective-module-direct-image-acyclic` has scheme/constant-coefficient and abelian higher-direct-image conclusions, so does not give this item. No new node is warranted for any of these existing facts.

## Blueprint and searches

Read the chapter/unit records and the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, clause (3). This is a supporting Leray-composition prerequisite below the existing alteration/cohomological-dimension branch recorded in the item's provenance. No unit or chapter is changed. `tools/blueprint_refs.py ancestor` reports `None` for the current created-item ancestry, as already recorded in the item; I retain that field and its detailed place/via chain, rather than inventing an imported ancestor. The existing nonempty place is retained, and `split_report.blueprint` explains how these steps serve it.

Whole-DAG searches covered 072Z, 0731, 03CR, their Stacks labels, totally acyclic, injective pushforward, ringed presentations, equivalence transport and enough injectives. Whole-blueprint searches used `injective`, `ringed topoi`, `03CR` and `terminal object`; none states this exact arbitrary-ringed-topos global-sections theorem in another form. The item's `same_as` remains empty.

Ran the required msearch command for the item using leanfinder (injective module pushforward/global sections without flatness), leansearch (arbitrary ringed topos), loogle (`SheafOfModules.pushforward, CategoryTheory.Functor.rightDerived`), and grep in `Algebra/Category/ModuleCat`. Read every result. Derived vanishing on an injective input requires the input to the sections functor to be injective, which is not assumed for f_*I. Local-injectivity hits concern maps of sheaves; ordinary pushforward hits do not assert this acyclicity. The prior item searches already use a second total-acyclicity phrasing and were read and retained. Also searched the site-presentation concept using all four command kinds before discovering its existing DAG node; those results remain in the log. No unrun search is claimed; no service returned unavailable during these new searches.

## Not duplicates

No new nodes. Existing presentation, module-equivalence, injective-embedding and site-evaluation theorems are cited directly. Terminal evaluation, transfer of the injective lifting property, compatibility of the induced scalar actions with a ringed natural isomorphism, and the resolution-level comparison are short arguments written in the item's proof rather than new statements.

## Review by Q24

I checked the unchanged item against the full statement and proof of Stacks 072Z and 0731(3). In particular the ringed-topos morphism is allowed to lack a presentation on its original sites; the replacement, rather than a restriction of the hypotheses, handles that case. I also read `sites-modules.tex`, Tag 03CR (`lemma-morphism-ringed-topoi-comes-from-morphism-ringed-sites`), especially finite limits in clause (5), the continuous finite-limit functor in clause (6), and the canonical ring transports. Tag 03D8 (`lemma-push-pull-composition-modules`) explicitly says its direct-image composition assertion follows from definitions; the scalar action check is written in step 3. For existence of resolutions I read the opening of `sites-cohomology.tex` section `section-unbounded` (07A5), and `injectives.tex`, Theorem 079H (`theorem-injective-embedding-grothendieck`); 079P was also read as the source of the stronger existing K-injective node. There are no new node statements requiring independent source checks.

Step 1 cites `prop-pur-kinjective-resolutions-exist` only for its assertion that modules over a commutative ring sheaf on an arbitrary small site form a Grothendieck abelian category. It does say this, not merely for schemes or constant rings. `lem-sp-grothendieck-enough-injectives` says every such category has enough injectives, supplying the hypothesis of the later evaluation result. I do not take K-injective computational properties from this citation.

Step 2 cites `lem-weil-pbc-ringed-topos-site-presentation`. Its statement supplies both small finite-limit sites, the two equivalences with canonically transported rings, the continuous finite-limit site functor, and a ringed natural isomorphism of the composites. These are precisely the data used, including the terminal target object. `lem-weil-pbc-ringed-presentation-transport` states in its initial module-adjunction clause that a ringed-topos equivalence induces an exact module equivalence. The later internal-Hom and local-completeness clauses are not used. The structural maps here are isomorphisms, so its ringed-equivalence hypotheses hold.

Step 3 is elementary from that exact equivalence and `def-sp-injective-resolutions`: I wrote the lifting problem, its image under the inverse equivalence, the extension to the injective I, and its transpose back. For the module comparison, the natural isomorphism in step 2 is ringed, so the composite structural maps coincide under it; induced direct images use precisely these maps for their scalar action, as stated in `def-weil-pbc-ringed-topos-morphism`. No claim about injectivity of f_*I occurs, and no new transport theorem is hidden here.

Step 4 reads and uses the entire conclusion of `lem-weil-pbc-ringed-site-direct-image-injective-evaluation-acyclic`: module-derived object evaluation vanishes for the pushforward of an injective module under a continuous site presentation without flatness. Its site names are interchanged explicitly, avoiding an inverse-image/direct-image direction mistake. The replacement functor preserves covers and finite limits, the rings are commutative, and step 1 supplies enough injectives in both module categories in the common universe. At the terminal object, the representable is literally the terminal presheaf and is a sheaf, since sheaf conditions into a singleton are unique. The section/natural-transformation correspondence and its inverse by restriction are written out. Applying that natural equality to the injective resolution is exactly `def-sp-left-exact-additive`, not an uncited change between abelian and module cohomology.

Step 5 is elementary from the previously supplied exact equivalence: its image of the chosen resolution stays exact, and the earlier lifting argument proves each image term injective. Full faithfulness and preservation of the terminal sheaf give the additive Hom bijections; their naturality makes them commute with the specified differentials. Thus there is an actual isomorphism of complexes of global sections, not just unrelated degreewise identifications. Taking cohomology uses exactly the injective-resolution definition in `def-sp-left-exact-additive`. The source and target resolution are module resolutions throughout.

For the B--E checks: there are no unsplit new nodes, duplicate clauses or fabricated Mathlib leaves. Every non-elementary input is a cited existing statement, and `citations.json` contains its verbatim wording rather than a paraphrase of a proof. No node used above reaches the item, so the added edges do not create a dependency cycle. Generic tools from other units are declared in `split_report.tool_uses` with their exact roles; no maintainer-owned `tool_uses` field is set. The five steps have fewer than 900 characters each, and each short equivalence/terminal calculation is explicit. I checked the zero module, zero ring sheaf, identity morphism, sites without a terminal object, and a morphism of point topoi induced by a non-flat ring map. Zero and degenerate cases stay valid; original sites need not have a terminal object because the replacement does; on point topoi global sections is exact even when restriction of scalars does not preserve injectives. No non-flat case or universe is excluded.

The principal correction made while drafting was to reuse the existing 03CR presentation instead of introducing a new presentation lemma. I also supplied enough injectives explicitly through the existing general ringed-site Grothendieck result, rather than citing the scheme/constant-ring version. Nothing remains unfinished in the requested one-level split. The required server dry run and direct delivery follow this report.
