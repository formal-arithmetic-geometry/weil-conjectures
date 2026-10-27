# Worker report: lem-sp-site-coherence-descent

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-site-coherence-descent.json`: statement, split; ten componentwise categorical proof steps. Mathlib verdict: no declaration states this full witnessed-input assertion or a one-line specialization. No new nodes and no new Mathlib leaves.
- `citations.json`: one verbatim statement citation for every node used by every proof step.
- `searches.jsonl`: actual search-command results for this item; inherited searches remain in the item unchanged, with the five searches run by Q128 appended.
- `report.md`: this report. `write_split.py` is a sandbox-only drafting script, not a delivery file.

## Attachments

None. Searched the project declarations for the exact blueprint tag, witnessed comparisons, common refining towers and coherence descent; no project declaration supplies every clause. The source's `CategoryTheory.conjugateEquiv_paste` and `conjugateEquiv_cocycle` in `CategoryTheory/Adjunction/ConjugatePaste.lean` concern mates under supplied adjunctions, which are absent here, and do not state the item.

## WANTED

None. The cited Stacks source and blueprint proof are available locally.

## What was wrong or missing

The item was statement-only and unsplit. Its statement and dependencies are unchanged. Its inherited categorical abstractions are hypotheses, including etale choice independence, compatible towers, etale composition coherence, and naturality at specified changes of witness. The proof must not silently replace these by theorems about geometric compactifications or claim naturality on arbitrary pro-side objects. The new proof makes the necessary cancellation calculations explicit.

Mathlib searches used the mandated command, with two semantic phrasings, Loogle, grep, and LeanSearch. The first semantic query returned general map-composition/congruence and small-object iteration results. The second returned iso-whiskering identities. Loogle returned functor associators/whiskering. Grep returned adjunction mate composition and hypercover refinements. LeanSearch returned pseudofunctor descent-data pullback constructions, which presuppose a pseudofunctor and concern categories of descent data rather than the given witnessed comparison families. I read `Functor/Category.lean` at associator (185), `Adjunction/Mates.lean` at conjugate composition (341--380), and `Sites/Descent/DescentData.lean` at the returned comparison definitions (268, 305, 341). These are useful elementary infrastructure, not matches for this item. Searches are recorded with the exact query strings and actual answer digests; none was invented. There are no unavailable services in this session's five searches.

## Not duplicates

No new nodes were created, hence no new/existing node pairs require comparison. Whole-DAG searches by the cited Stacks tags and conjugation/cofiltered refinement keywords, and whole-blueprint searches for witnessed inputs, refinement and comparison pastes, found no second blueprint node stating this abstract witnessed result. Existing geometric refinement and composition statements are applications with additional geometric hypotheses, not replacements for the generic item. No new node restates a clause, and no elementary cancellation was made a separate node.

## Review by Q128

I read Stacks `more-etale.tex`, Tag 0F7I `lemma-shriek-well-defined` (including its cancellation footnote), Tag 0F7J `lemma-shriek-composition` (tower construction and independence comparison), and Tag 0F7K `lemma-pseudo-functor` (both triple pastes). These sources motivate the route; they do not themselves state the abstract witnessed comparison lemma. Accordingly `proof_origin.by` is `agent`. I also read the current ancestor blueprint's `det-sp-reduction-exceptional` proof, especially Locality, the parent split `lem-sp-finite-compact-site-coherence`, the chapter record and the unit `sk-thm-sf-compatibility`. This item realizes only the generic descent part of the parent's Step 3, with the two comparison equations supplied by its earlier steps. It neither changes the unit route nor introduces the forbidden SGA route.

For every proof step I opened the one cited statement, `def-nagata-category`. It explicitly gives identity and associativity laws for composition; those are the only externally cited facts used. Functoriality, naturality, inverses, cofilteredness, witness changes, etale coherence and comparison equations are explicitly supplied or defined in the item's statement. Thus no step takes a theorem from a definition that does not state it. `citations.json` quotes the actual definition statement verbatim ten times, once per step. The definition is already a Mathlib leaf and is a generic category-law tool, so it requires no off-unit route substitution.

Step 1 spells out cancellation and preservation of inverses from the category and functor laws. Step 2 solves the refinement square and multiplies out its inverse, then cancels intermediate comparisons along a zigzag. Step 3 explicitly computes the common-source comparison and its cocycle law; common-source existence and etale path independence are exactly the hypotheses. No colimit or small index category is invoked. Step 4 solves the assumed tower square for the binary map and writes its inverse; it does not assume invertibility away from the image.

Step 5 checks all domains in the composite input comparison. Its use of naturality of a pro comparison at `C_f` is exactly the stipulated change from the witness `N_Y E_f E` to `P_f N_X E`. The other interchange is ordinary naturality of `C_g'` at the etale arrow `t_f`. The displayed formula `S B = B' N(t)` therefore needs neither fullness nor faithfulness. Step 6 substitutes this formula into the actual move-to-tower/move-back paste and gets `A B = C N(alpha)`; the last equality uses only the statement's etale descent hypothesis. The formula no longer contains a chosen tower, so it proves independence even without constructing a triple tower.

Step 7 expands the left triple path and uses naturality of `C_h` at the actual arrow `alpha^e_{g,f}`. Step 8 expands the right triple path and uses the same stipulated witness naturality as Step 5, now for `A_{h,g}`. The two resulting etale paths agree by the explicitly assumed etale associativity. Both pro paths agree after precomposition by the displayed invertible `D`, which is cancelled in the output category. Nothing cancels the functor `N`. Step 9 checks identity candidates under the specified identity identifications and `C_id = 1`, then writes the component argument for naturality of inverses and composites. Step 10 gives the exact witness-conjugation formula, its inverse and the cancelling middle factors, and checks the intervening witness is `P_f(xi) C_f(E)` as required by the statement.

I tested the small cases: terminal candidate categories reduce to the binary square; identity arrows reduce to `C_f C_f^{-1}`; an empty etale category gives vacuous assertions; a functor with nonfull image still permits every calculation because all input arrows used are supplied etale arrows or specified witness changes. For distinct unrelated witnesses, the proof makes no unstated comparison between them. Parallel refinement choices are covered by the assumed etale independence, not by faithfulness of `N`. Multiple towers give the same solved binary formula. No essential-surjectivity, smallness, coefficient or base-field hypothesis was added.

I checked delivery-errors B--E: all notions are introduced in the statement or its cited category definition; all sources are identified by correct Stacks tags and labels; TeX uses single mathematical backslashes; there is no statement-only new node containing a proof; no hidden theorem is quoted by tag; no new duplicate or clause-as-node was created; every nontrivial coherence input is a stated hypothesis and every deduction is an explicit elementary calculation. All ten steps are shorter than 1000 characters, so none exceeds the 2000-character review threshold. The statement, inherited citations and search records, creation record, blueprint ancestry and unit fields were retained. The item has `same_as: []` after the blueprint search. No Lean source, compiler, Lake, repository file or launcher file was written or run.

## What could not be finished

Nothing mathematical remains in this one-level split. The required server preflight and dry run determine delivery readiness.
