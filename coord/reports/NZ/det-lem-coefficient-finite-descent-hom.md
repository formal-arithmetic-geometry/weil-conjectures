# Stage-1 report: det-lem-coefficient-finite-descent-hom

## Files written

- `dag/nodes/sec-six-functors-basics/det-lem-coefficient-finite-descent-hom.json`: the item, split into the three proof paragraphs of the current main-20261015 blueprint; no new statement nodes were needed.
- `citations.json`: five verbatim statement quotations covering every proof-step citation.
- `report.md`: this report. The authentic `searches.jsonl` was produced by `msearch.py`.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact item id, finite-coefficient descent/Hom names, and the related two-colimit declarations. No sorry-free project declaration states this item. The upstream master checkout is reference material only and likewise supplies no attachment.

## WANTED

None. The blueprint source and all cited DAG statements are available locally. No SGA source is used.

## Corrections and limitations

There is no statement dispute: the item statement is retained exactly as imported from `sk-lem-coefficient-finite-descent-hom.md`. The only proof repair is to make the existing derived extension/restriction adjunction explicit in step 1 by citing `sk-def-sfb-derived-extension-of-scalars`; the finite and completed flatness statements justify replacing the derived tensor by ordinary tensor. The coefficient colimit and constructible Ext-continuity nodes are cited directly in steps 2 and 3. The cross-unit generic adjunction is declared in `split_report.tool_uses`, rather than moved into a new node or used to replace the unit's route.

No new node restates a clause of the item. The Mathlib searches found only generic derived-category, Ext, filtered-limit, or ordinary `ModuleCat` scalar-adjunction declarations, so the item is not a Mathlib leaf. All searches recorded in the item were actually run with `msearch.py`, including second phrasings for each search kind.

## Review by NZ

I read the chapter record, the `sk-thm-sfb-qlbar-two-colimit` unit record, the item's current blueprint file, and the five cited node files. Step 1 uses `lem-sfb-subfield-flat` for finite-stage flatness, `lem-sfb-qlbar-flat` for completed-coefficient flatness, and `sk-def-sfb-derived-extension-of-scalars` for the derived extension/termwise restriction adjunction. Their statements say precisely that the two scalar extensions preserve finite limits and that derived extension is left adjoint to exact termwise restriction. The hypotheses match the item's finite extension and standing-scheme setting. Step 2 uses the displayed `\QbarX\cong\varinjlim_E E_X` clause and filtered finite-subextension poset in `sk-prop-sfb-qlbar-colimit-x`; tensor-colimit compatibility and preservation of the lower bound then give the stated filtered complex system. Step 3 uses the canonical filtered-colimit Hom isomorphism in `sk-lem-constructible-ext-continuity`, with `C\in\Dbc(X,E)` and the common lower bound supplied by step 2; the adjunction identifications from step 1 and the representing-complex identification from step 2 give exactly the displayed map.

For C4, I copied the complete current statements into `citations.json`, so each quote is a verbatim part of the node it cites. For C1, the only non-elementary facts are the three existing results just named; the compatibility of transition maps and the termwise lower-bound observation are elementary once those statements are in place. I checked that no cited node is being used for its proof rather than its statement. I tested the limiting cases of the zero complex, identity extension, and the lowest degree of a bounded representative; the formulas remain defined and the lower-bound assertion is unchanged. No hypothesis was added or dropped, no SGA route was introduced, and no cycle-producing dependency was added.

## Unfinished work

None for this one-level split. The second worker should independently reread the item, its three source paragraphs, and every quoted dependency before delivery.


## Second reading by NZ

- Item statement: compared all three clauses and each hypothesis with current `main-20261015/.../sk-thm-sfb-qlbar-two-colimit/sk-lem-coefficient-finite-descent-hom.md`, and its parent unit's paragraph (2); PASS, statement retained verbatim. Read the separate `.proof.md` and the chapter route. Standing means separated finite type over the fixed characteristic-$p$ field with $p\ne\ell$, as specified by `sk-def-sfb-dc-setting`.
- Step 1: checked the statements of `lem-sfb-subfield-flat`, `lem-sfb-qlbar-flat`, `sk-def-sfb-change-of-scalars`, `sk-def-sfb-sheaf-tensor` and `def-weil-abstract-derived-category` against the first source paragraph; REPAIRED. Flatness supplies finite limits, the ordinary left adjoint supplies right exactness, and exact restriction is explicitly stated. The unit/counit descend to the localization and retain their identities. Wrote the balanced transitivity isomorphism, its inverse and the equation $\alpha_{B'}(f_{B'})=t_{D[r]}\alpha_B(f)$, also for $B'=\QbarX$. These short calculations replace the unproved assertion that scalar adjunctions are compatible.
- Step 2: checked `sk-prop-sfb-qlbar-colimit-x` (which states a ring colimit, not a module colimit), `det-def-sfb-qlbar-condensed-subextensions`, `sk-def-sfb-sheaf-tensor`, `def-sfb-modobj-relative-tensor` and `lem-weil-pbc-module-sheaves-colimits-forgetful` against source paragraph (2); REPAIRED. Read the latter's Stacks sources in `sites-modules.tex`, Tags 03DA/03DB, labels `lemma-abelian`/`lemma-limits-colimits`. Wrote the cofinal-cocone construction $H\mapsto EH$, common-stage ring operations on the module colimit, the coequalizer/colimit universal-property calculation, and compatibility with the differential. The lower bound is termwise zero, with no assertion that a derived-category colimit is being taken.
- Step 3: checked the current full `sk-lem-constructible-ext-continuity` statement, `sk-def-sfb-dc-setting`, `sk-def-sfb-bounded-constructible`, and `lem-weil-pbc-finite-type-over-noetherian`; REPAIRED. Read `morphisms.tex`, Tag 01T6, label `lemma-finite-type-noetherian`, with its Noetherian-base and finite-type hypotheses. A field has only two ideals and a one-point spectrum; thus the cited theorem makes the standing $X$ Noetherian. Continuity explicitly includes all bounded constructible $C$ over $E$. The proof now constructs a bounded representative from cohomological boundedness and checks the small filtered index, common lower bound, coefficient choice and arbitrary integer shift. The step-1 equation identifies the resulting map with the requested extension-of-scalars map.
- New nodes: none; B1–B7, duplicate/specialization checks and the Mathlib-leaf classification introduce no new obligations. Existing generic tools supply all extra citations; no clause was moved into a new node.

Changes and reasons:

- Preserved the item's statement and the first worker's report sections. Added the missing statement-definition dependencies for the standing setting, bounded constructibility, pulled coefficients, module objects, scalar operations and ambient derived category.
- Replaced the unnecessarily general K-flat derived-adjunction citation by the ordinary scalar adjunction plus its explicit exact-functor localization argument. This checks every hypothesis using flatness and exact restriction already available here; it does not need an additional flat-resolution assumption. No new adjunction node is justified by this few-line argument.
- Expanded the three proof steps as listed above to repair C1/C3/C4/E1/E5 gaps. The route is still scalar adjunction, termwise coefficient colimit, and constructible Ext continuity. The unit and chapter statements and routes are unchanged.
- Updated `proof_deps`, refreshed `citations.json` to fourteen complete verbatim node-statement quotes, and recorded each outside-unit generic tool in `split_report.tool_uses` for the maintainer's judgement. Did not write the maintainer-owned `tool_uses` field. Every cited existing node was read; a dependency traversal found no path from any added dependency back to this item.
- Corrected `proof_origin` to the actual separate `.proof.md` file: the source `.md` has no `## Proof`. The summary and blueprint realization now describe the expanded proof.
- Ran fresh `msearch.py` queries in LeanFinder, LeanSearch, Loogle and grep, with different phrasings. LeanFinder returned ordinary module/sheaf adjunctions, LeanSearch returned generic colimit infrastructure, and the valid Loogle query found `CategoryTheory.Adjunction.localization`. Read `Mathlib/CategoryTheory/Localization/Adjunction.lean`, lines 15–108: this is generic infrastructure, not the three-clause coefficient-descent statement. The earlier and fresh rejected Loogle queries are recorded as inconclusive rather than no match. Filled the item's empty `mathlib_searches` from the authentic log, including the original worker's queries; no complete-item Mathlib leaf was found.
- Independently searched the read-only slopmaster2 `WeilConjectures` and `Comparator` by item id, the parent unit's `constructibleCocone_homSurj`/`homInj` names, and coefficient-descent/Ext-continuity vocabulary. No exact project declaration to attach was found. Upstream master sorry declarations were not treated as finished proofs.
- Terminology correction to the earlier report: $\Qlb$ here is the algebraic closure with the stipulated filtered-union condensed coefficients, not its completion. The proof does not replace it by a completed coefficient field.

Small cases checked: $C=0$ or $D=0$ gives zero Hom groups throughout; $F=E$ makes the scalar adjunction the identity adjunction, and $F\prime=F$ makes transition maps identities; $X=\varnothing$ gives the zero module category; on a field-valued point with $C=D=E_X$ in degree zero, the map is the stipulated union of finite fields into $\Qlb$. A single-degree representative has the asserted lower bound, with $a<b$ chosen by padding with zero terms, and negative, zero and positive shifts all use $q=r$ without altering the common lower bound of the unshifted diagram. None changes a source hypothesis. No SGA source, Lean edit, compiler, Lake, manual git command, live-project write or sub-agent was used.

The brief's trailing `.` is not accepted by this installed `deliver.py`; it prints usage. Used the documented two positional arguments with `--no-push` for the dry run, and the same two arguments without that flag for delivery.
