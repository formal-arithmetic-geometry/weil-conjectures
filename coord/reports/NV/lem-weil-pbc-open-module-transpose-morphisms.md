# Worker report: lem-weil-pbc-open-module-transpose-morphisms

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-open-module-transpose-morphisms.json`: statement node, now split into six elementary steps. The statement, source, existing searches, created record and blueprint ancestry are retained. Six actual search-log entries were appended. Mathlib verdict: no whole-item match.
- `citations.json`: one verbatim statement quote for every step/node citation (six entries).
- `report.md`: this report. `searches.jsonl` is the unmodified search command log; `prepare.py` is sandbox-only preparation code.

New nodes: 0. New Mathlib leaves: 0. No Lean files, compiles, builds or repository writes.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag, transposes of module morphisms, open restrictions and adjunctions. There is no tag match or declaration stating all the clauses for module presheaves on an arbitrary ringed topological space. The inspected `Algebra/Homology/OpenRestrictionAdjunctionExact.lean` proves exactness and the extension-by-zero LEFT adjunction, not these explicit formulas for the direct-image RIGHT adjunction. It is not an attachment. Mathlib's `PresheafOfModules.Hom` and `restriction` are definitions and component constructions, not the whole item.

## WANTED

None. The sources needed are available locally.

## Audit of the imported item and route

There was no existing sandbox node or report to resume and no released repair note for this item. The live node was statement-only. No mathematical correction to its statement was needed. In particular, the stipulated sectionwise structures are hypotheses here; I do not cite the parent adjunction or the sibling section-functor lemma to prove them. Doing so would risk a cycle. Step 4 directly checks that the prescribed actions on morphisms yield morphisms, rather than assuming that silently.

Read `GOAL.md`, the three levels of `SETUP.md`, the stage-1 brief, the worker role, stage-1 rules, chapter `sec-proper-base-change` and unit `sk-thm-p1`. Read the current main-20261015 ancestor proof and its `blueprint_update`; its finite-pushforward step is the inherited service for the chain that leads to the present local adjunction check. No chapter or unit route is changed. This item is not a key node, so no unit realization field is edited.

Whole-blueprint searches for `transpose`, `008U`, `open restriction` and `module presheaf`, and DAG searches by tags and transposes, produced no blueprint statement equal to the item. The parent `lem-weil-pbc-ringed-space-open-restriction-adjunction` uses this item and is not usable below it. Existing definition nodes suffice for the proof. No new node is needed for an elementary calculation.

The Mathlib searches were made with `msearch.py`, in two semantic phrasings plus Loogle, LeanSearch and two grep queries. All hits returned by the commands were read. Inspected `Mathlib/Algebra/Category/ModuleCat/Presheaf.lean`, lines 43–128 and 290–301: semilinear maps, the `Hom` structure with its naturality law, componentwise composition and the single restriction natural transformation. These do not already construct the two open transposes in the statement. Other hits concerned modules on schemes, tilde modules or ringed-space structure presheaves, and thus neither cover arbitrary module presheaves nor all of the displayed identities. The six original log records remain in `searches.jsonl`; the item's seven inherited searches were preserved as history.

## Not duplicates

No new nodes; no new/existing same-tag pairs to justify.

## Review by NV

I read the item source `literature/stacks-project/sheaves.tex`, Tag 008U, label `lemma-adjoint-push-pull-presheaves-modules`, statement and entire proof at lines 2782–2833. It describes the forward transpose by direct image followed by the unit, the reverse by pullback followed by the counit, and leaves compatibility with the module structures to the reader. I also read Tag 00A0, label `lemma-j-pullback`, statement and proof at lines 4453–4494. Its open section model applies explicitly to modules; (1) gives the presheaf restriction and (2) addresses sheaves. Checked both tag/label pairs against `tags/tags`. The six steps supply the omitted module and naturality computations, rather than using the Stacks adjunction as an unproved black box.

For steps 1–5 I opened and read the full statement of `def-weil-presheaf-modules-sheafification`. Its first sentence defines precisely the additive presheaf, sectionwise module actions, semilinear restrictions and sectionwise linear morphisms that these steps use. No step takes any sheafification comparison or existence result from that definition. Its morphisms are morphisms of abelian presheaves, so their restriction naturality is part of their definition. For step 6 I opened `def-weil-sheaf-of-modules-category`; it defines sheaves of modules and their morphisms with precisely the same restriction and linearity conditions. All six quotes in `citations.json` are literal substrings of those statements. These are definitions/Mathlib leaves, so their use from another unit is not an off-route theorem invocation.

Step 1 checks additivity and the scalar equation using the actual restricted scalar action on DQ; in particular it does not falsely treat the restriction P(V) -> P(V intersect U) as linear over the smaller ring without restricting scalars. Step 2 checks naturality for an arbitrary inclusion V' in V, writing both iterated restrictions and identifying the DQ restriction. Step 3 uses W intersect U = W and rho_W = id exactly where W is contained in U, so beta_W has the correct scalar ring; its naturality equation uses inherited restrictions. Step 4 checks Rmu and Dnu as morphisms and expands the forward composite, and step 5 expands the other composite and applies the naturality of mu. The resulting expressions agree on every section, giving the required equality of component families. Step 6 checks both sheaf conditions by the same covers and the intersected cover, so the specialization to module sheaves adds no unproved preservation assertion.

I checked every case in delivery-errors B–E against the node and these sources. The statement introduces all of its objects and already cites both notions; TeX escapes and tag labels are retained correctly. There are no new standalone clauses or relabelled lemmas, no hidden general theorem, no tag used as a substitute for a node, and no reference to another node's proof. Each elementary step is a direct computation or cover-gluing check from the cited definitions and the item's hypotheses. Every step is shorter than 700 characters; none exceeds the long-step threshold.

Small cases checked: U = X makes rho the identity and both transposes componentwise unchanged; U empty still allows arbitrary module PRESHEAF values on the empty open, and the formulas use actual restrictions to the empty open, with no assumption those values vanish. For sheaves the gluing argument includes the empty cover and hence forces the required unique empty section. If V is disjoint from U the formula is still alpha_empty composed with restriction to empty. Identity and zero morphisms obey the composition formula, as do zero modules and the zero ring. Neither finiteness nor injectivity nor nonemptiness is used. No disputed statement or unfilled proof obligation remains in this item.

## Unfinished work

None for the one-level split. The existing definition dependencies retain their own records. Required server validation and direct delivery follow this report.
