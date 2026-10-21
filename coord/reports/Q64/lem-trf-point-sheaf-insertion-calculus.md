# Stage-1 report: lem-trf-point-sheaf-insertion-calculus

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-point-sheaf-insertion-calculus.json`: statement node, split into seven steps; no exact Mathlib match.
- `citations.json`: one verbatim statement excerpt for each of the thirteen step/node citations.
- `report.md`: this report. `searches.jsonl` contains the actual search-command results.

New nodes: 0. New Mathlib leaves: 0. The item statement and `stmt_deps` are unchanged, as are all maintainer-owned fields. There was no earlier sandbox split or report to repair.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag/id and for point insertion/transport terminology; no declaration states every clause. The generic upstream pullback-composition declarations do not state this normalized point-section and complex calculus. I wrote no Lean and ran no compiler or build tool.

## WANTED

None. The blueprint, Stacks sources and Deligne convention needed here are available locally.

## What changed and why

The original node was statement-only. Its inherited Mathlib searches were retained. I supplied an actual proof rather than introducing new nodes for its individual clauses. The existing `lem-sfb-proetale-object-inverse-image-restriction` already gives the precise graph-index coprojection and the sheafification comparison. `lem-weil-sheaf-scalar-extension-ring-iso` gives the normalized tensor comparison. `lem-trf-constant-coefficient-composition` already supplies the finite constant-ring compositor equation in this same unit, so no additional coefficient lemma or inverse-system detour is needed. The normalized generic sheaf and module compositor nodes give the remaining composition input.

The important calculation is in step 4: the two graph maps have coordinates `(u, hu, id_U)` in the iterated fibre product, and its canonical map to the direct fibre product retains `(u, id_U)`. Together with `(y tensor 1) tensor 1` mapping to `y tensor 1`, this proves the specified compositor identity. Steps 5–6 then compute the section insertion and its composition through actual restriction maps. Step 7 checks the differential and chain-map equations degree by degree.

No source or statement dispute was found. No clause was weakened, no hypothesis was added, and no integral or rational coefficient category was substituted for finite constant module sheaves. Nothing is left unfinished mathematically at this one-level split.

## Searches and reuse

Searched the whole DAG for the tags 03CE, 06UM and 03CB and for reindexing, comma indices, object restriction, inverse-image composition and tensor units. Opened the full statements of each selected dependency; also examined the nearby isomorphism-inverse-image, scalar-composition and point-transport nodes. A transitive dependency traversal found no path from any selected theorem back to this item.

Ran `tools/blueprint_refs.py ancestor lem-trf-point-sheaf-insertion-calculus`, which identifies `lem-trf-frobenius-operator-compact-description`. Blueprint searches included `pullback composition`, `insertion`, `point transport`, `normalized sheaf insertion`, and `automorphism colimit`. They find no blueprint node stating this entire item. The point-transport hits concern other coefficient or trace constructions; they do not give this graph-normalized ordinary module-sheaf statement. No new node was created.

All new Mathlib searches were executed through `msearch.py` and recorded verbatim from `searches.jsonl`: two LeanFinder formulations, Loogle `SheafOfModules.pullbackComp`, the grep pattern `pullbackComp|pullbackObjFreeIso|conjugateEquiv_pullbackComp` in `Algebra/Category/ModuleCat/Sheaf`, and the recorded LeanSearch query. All services returned results, not unavailable errors. I read `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:167–182` and `PullbackFree.lean:118–142`: the former constructs the generic adjoint compositor, and the latter concerns free sheaves. Neither is an exact match or a one-line specialization giving all item clauses. The second LeanFinder formulation returns generic site/sheafification compatibility maps, likewise insufficient for the whole item.

## Not duplicates

No new nodes; therefore there are no new/existing pairs to justify. Existing lemmas are cited directly, including the same-unit constant-coefficient composition lemma.

## Review by Q64

I read the chapter `sec-trace-formula` and unit `sk-d-weil`, the three-level route rule in SETUP, and the current main-20261015 statement/proof of `lem-trf-frobenius-operator-compact-description`. Its paragraph beginning “That action transports the pair” is the ancestor location realized here. This is a finite ordinary-sheaf calculation below that transport route, not a change to the unit or chapter. I read Stacks `sites.tex`, Tag 03CE (`lemma-localize-given-products`), Tags 00VE/00WX (`lemma-adjoints-u`/`lemma-adjoint-sheaves`), Tag 03CB (`lemma-composition-morphisms-sites`) and Tag 06UM (`section-pullback`); `proetale.tex` Tag 09A5 (`section-morphism`); and `sites-modules.tex` Tag 03CZ (`lemma-adjointness-tensor-restrict`), Tag 03D3 (`lemma-adjoint-push-pull-modules`) and Tag 03EK (`section-tensor-product`). Deligne Weil II (1.1.7), printed pp. 150–151, was read from PDF pages 14–17: it fixes geometric Frobenius and transport of structure, but does not itself state the graph-index refinement. Accordingly the proof is explicitly agent-written from the cited constructions. There are no new node statements to source-check.

For step 1, I opened the statements of `lem-weil-iso-weakly-etale` and `lem-sfb-proetale-object-inverse-image-restriction`. The first applies to each power of the scheme isomorphism h. The second applies because `(s,h^r)` is consequently an object of the pro-etale site, and explicitly gives the initial index `(U,h^r u)` with graph `(u,id_U)`, the presheaf isomorphism, the invertible sheafification map, and the ring/action comparison. Its assertions apply to all sheaves here, without a finite-stalk or constructibility condition. This is a theorem application, not an elementary assertion or an appeal to its proof.

For step 2, I opened `prop-weil-pbc-proetale-constant-ring-map` and `lem-weil-sheaf-scalar-extension-ring-iso`. The former says the particular constant-section-preserving coefficient map is invertible, for finite A and hence for our finite commutative A. The latter is for any small site, any isomorphism of commutative ring sheaves and any module sheaf; it states both the pure-tensor formula and the inverse `m` to `m tensor 1`. Thus it gives exactly the normalization, naturality and module linearity used here. Transport through step 1 identifies the intended scalar action, and no unspecified isomorphism is substituted.

For step 3, I read `lem-trf-constant-coefficient-composition` and `lem-sf-proetale-tensor-composition-unit`. The former is in sk-d-weil, accepts arbitrary composable scheme morphisms and finite commutative A, and states exactly the coefficient-map equality used, with alpha oriented opposite to a. The latter accepts these canonical ring isomorphisms and states that its explicit tensor comparison is the actual adjunction-compatible module compositor, including its local generator formula and inverse. Its hypotheses are now all available. This checks that T is oriented from successive to direct pullback, and that the two scalar units really map to one scalar unit.

For step 4, the statement of `lem-trf-site-inverse-image-composition-generators` gives the normalization on nested coprojections, on abelian sheaves as well as sets, with compatibility under restrictions. The smallness and sheaf-preserving hypotheses come from the compatible skeletons and base-change functors of the item's fixed inverse-image construction. I checked `def-pc-fibre-product`: its universal property and induced-map formula justify the coordinate calculation `(u,hu,id_U)` to `(u,id_U)`. The same module-compositor theorem cited in step 3 handles the intervening tensor comparisons and the two scalar units. Equality is checked on every actual section of R_(m+1)F, not on a falsely assumed single representative of a general sheafification. All three cited statements say precisely what is used.

For step 5, I read the definitions of a module-sheaf morphism and constant sheaf. The restriction/morphism square follows from naturality of that morphism; constants restrict identically, so the restriction is A-linear. The graph at the final object is literally `(id_s,id_s)`. The identity j = rho composed with restriction and the ensuing naturality calculation are elementary consequences of steps 1–2 and those definitions.

For step 6, I checked the intermediate domains rather than writing “transport commutes.” In particular the R_mF restriction along h is the F restriction from `(s,h^m)` to `(s,h^(m+1))`. Its composite after restriction along h^m is restriction along h^m h. The explicit equation in the step uses the already proved compositor identity, site naturality of e, then presheaf functoriality and cancellation of an isomorphism. The cited module-sheaf definition includes the underlying presheaf, so there is no additional geometric lemma hidden here.

For step 7, the opened `def-weil-abstract-derived-category` states the definition of complex and componentwise chain-map equation. Naturality from step 5 applied to each differential supplies that exact equation; applied to each chain-map component it supplies naturality on complexes. The comparison with R shows H preserves addition and zero, so termwise application is a complex. Step 6 in each degree gives the final equality. This is an elementary use of established equations and definitions; it does not use a resolution, quasi-isomorphism comparison or unproved exactness of evaluation.

I checked delivery-errors B–E throughout. No new nodes restate a clause, no unsplit node has a hidden proof, all thirteen citations have verbatim statement excerpts in citations.json, and no non-elementary ingredient is merely quoted by tag. All seven steps are below 2,000 characters. Off-unit statement tools are declared with individual reasons in split_report.tool_uses; the isomorphism-to-weakly-etale fact and the definition nodes are existing Mathlib leaves. No SGA route is used.

Small-case checks: for h = id all graph indices reduce to the identity section and every displayed formula reduces to the tensor unit comparison; for m = 1 the two restrictions are explicitly h followed by h. At U empty, additive sections and all maps are zero, so the graph and tensor normalization still hold. For F = 0 or the zero coefficient ring the formulas remain the unique zero maps. For F = A_s the scalar comparison fixes each constant a, checking the A-linearity convention. A complex concentrated in one degree reduces to the sheaf calculation; an arbitrary differential is handled by the displayed naturality square, so boundedness is not smuggled in. For nontrivial h I kept `(s,h^r)` and `(s,id)` distinct, with exactly the specified restriction map between them. The construction does not rely on the field automorphism being Frobenius or on finite-dimensional sections.

Corrections during self-review: used the existing same-unit constant-coefficient-composition theorem instead of adding a duplicate or invoking a stronger inverse-limit theorem; separated sheaf and tensor normalizations before the graph calculation; and wrote the intermediate `(s,h)` component in step 6 to fix all restriction domains. There was no earlier returned delivery. The server-only check_dag run passed with “no finding introduced by the sandbox or on its nodes”; the required delivery dry run and push follow this report.

The first delivery dry run rejected only the short quote for the constant-ring isomorphism. I expanded that quote to include the construction of c_u and its invertibility assertion verbatim, without changing the proof, and reran the dry run.
