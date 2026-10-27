# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-ringed-topos-relative-tensor-pullback.json`: statement, split using existing nodes; no Mathlib match.
- `citations.json`: one verbatim statement quotation for every step/node pair.
- `report.md`: this report. `searches.jsonl` contains the actual search-command records; `prepare.py` is sandbox scratch only.

No new nodes; no Mathlib leaves. The sandbox had no node or earlier split to resume.

## Attachments

None. Searched `lean/WeilConjectures/` by the exact blueprint tag and by relative tensor, tensor/pullback, and K-flat names. The exact tag is absent. The topological pullback construction in `Algebra/Homology/KFlatPullback.lean` concerns spaces with their open-set sites. The finite-coefficient and module-object monoidal comparisons found under `SixFunctors/ProEtale/` do not state this arbitrary-ringed-topos mixed relative tensor identity. No declaration found covers all clauses.

## WANTED

None. The proof and its K-flat prerequisites are available in `literature/stacks-project/sites-cohomology.tex`.

## Errors or discrepancies

The item statement is unchanged and agrees with Tag 08I6 (`lemma-variant-derived-pullback`). There is no statement dispute. The source ends “The lemma follows from this and the definitions”; the delivery expands the choices, scalar actions, differential, and localization needed for that sentence. In particular it never assumes that restriction of an A-flat or A-K-flat object is C-flat or C-K-flat for C = f^{-1}B.

The inherited blueprint ancestor is null: `tools/blueprint_refs.py ancestor` prints None for this provenance chain. I retained that existing field, its via list, and the detailed source place rather than inventing a blueprint id. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, in particular (3), and the chapter/unit records. This is a generic tensor identification below that route, not a new route to constructibility. Whole-blueprint searches for `08I6`, `relative tensor derived pullback`, `inverse image K-flat`, and `K-flat resolution` gave no alternative blueprint node stating this item. Tag/key-word DAG searches found the existing tools cited by the proof.

## Unfinished work

None within this one-level split. All used lemmas are existing DAG nodes. Their own proof completion is outside this stage-1 item.

## Review by Q33

I read the statement and full proof of Stacks Tag 08I6 and the surrounding constructions: Tag 06YS (`lemma-K-flat-resolution`), Tag 0G7E (`lemma-pullback-K-flat`), Tag 06YY (`lemma-derived-base-change`), Tag 06YP (`lemma-K-flat-quasi-isomorphism`), Tag 06YT (`lemma-derived-tor-quasi-isomorphism-other-side`) and the construction preceding Tag 06YU (`definition-derived-tor`). There are no new nodes whose sources need separate checking. The current blueprint supplies the place in the inherited application route, while Stacks supplies this tensor argument. No SGA source is used.

For Step 1 I opened the statements of `lem-pc-kflat-resolution`, `lem-weil-pbc-ringed-pullback-preserves-kflat`, `lem-weil-pbc-ringed-topoi-derived-pullback`, and `lem-weil-pbc-site-derived-tensor-descent`. The resolution lemma explicitly includes flat terms. The preservation lemma is for arbitrary geometric morphisms on small sites, not only scheme maps; applying it to the intermediate ringed topos with ring f^{-1}B is legitimate. The pullback computation explicitly gives the canonical comparison on those models, and tensor descent gives the actual derived tensor object. No flatness of the structural ring map is among their hypotheses. This verifies the two separate K-flat claims about H and f^*Q, rather than confusing them.

For Step 2 I checked the same resolution and descent statements and the entire statement of `lem-weil-pbc-total-tensor-homotopy-cone-signs`. Its final clause says tensor with a K-flat factor preserves every quasi-isomorphism with arbitrary endpoints, in both positions. This permits a new C-K-flat resolution of the restriction of P, even though that restriction need not itself be C-K-flat. The comparison only identifies the underlying C-derived object; the A-linear functor is supplied by the P tensor H model and its descent in Step 4. Thus no A-action is silently assigned to the auxiliary resolution R.

For Step 3 I opened `def-pur-sheaf-tensor-product` and `def-pc-tensor-complex-sheaves`. They give sheafification of sectionwise tensor and the direct-sum total with its (-1)^p sign. The written balanced maps are inverse on generators, respect restriction and A-action, and have the same displayed differential. This is elementary from those definitions and does not require another lemma node for ordinary associativity. The argument does not assume that a sheaf tensor's sections equal a sectionwise tensor: the presheaf maps are sheafified.

For Step 4 the tensor homotopy/cone statement supplies quasi-isomorphism preservation, the derived pullback statement supplies quasi-isomorphism preservation between the Q models, and tensor descent supplies the resolving-class localization equivalence. The first variable and the second variable are localized separately, over A and B respectively; the product of these equivalences is an equivalence. The square on generators is written, and its validity after inverting quasi-isomorphisms follows by multiplying a commuting square by those inverses. The A-action remains present throughout because all comparison maps are A-linear; exact scalar restriction detects the quasi-isomorphisms on the unchanged underlying abelian sheaves. This proves naturality for derived morphisms, not merely for a selected complex map. These generic tools are declared in `split_report.tool_uses` since their home units differ.

I checked B–E against the delivered file. There are no new statement-only nodes, duplicate nodes, or clauses relabelled as lemmas. Every non-elementary input has an existing cited statement; each is quoted verbatim in `citations.json`, with no appeal to a cited node's proof. The item and its existing dependencies are self-contained on small sites, and the comparisons are isomorphisms in D(A). Mathlib searches used only msearch.py, with two semantic phrasings, Loogle, LeanSearch and grep. Their hits give underived pullback or module extension composition (including `SheafOfModules.pullbackIso`, `SheafOfModules.pullbackComp`, `ModuleCat.extendScalarsComp`), rather than this unbounded sheaf-theoretic identity. A follow-up grep read their actual declaration lines. Existing search records were retained; new entries are copied from the command's real log.

For small cases I checked f the identity with unchanged rings (the A tensor unit identity), either input zero (both complexes zero), and f the identity topos with the nonflat quotient Z -> Z/2 and E = G = Z/2 in degree zero. Both sides then retain the same Tor contribution; replacing the derived tensors by ordinary tensors would fail. This checks why C-restriction of P is not claimed K-flat and why no flatness assumption is needed. The maps also work for the zero ring and arbitrary unbounded complexes, since the construction uses direct-sum totals without interchanging infinite products. All four proof steps are below 2000 characters, and none contains a hidden standalone comparison lemma: the only comparison constructed is the item's own balanced map. No cycle is introduced by a new node. The source, hypotheses, citation scope, retained A-action and canonical-map normalization were all checked as described above.

## Not duplicates

No new nodes were created. Existing nodes supply all prerequisites. The occurrences of 08I6 in the proper-support projection and perfect-image nodes are application sites; `def-sfb-space-derived-tensor-pullback` supplies the algebraic-space operation setup and does not prove this arbitrary-ringed-topos identity.
