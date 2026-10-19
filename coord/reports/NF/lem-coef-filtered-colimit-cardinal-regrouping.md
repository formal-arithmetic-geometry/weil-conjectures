# Stage-1 delivery: lem-coef-filtered-colimit-cardinal-regrouping

## Files written

- `dag/nodes/sec-six-functors/lem-coef-filtered-colimit-cardinal-regrouping.json`: statement item, now split into eight steps; statement and statement dependencies retained verbatim. Not a Mathlib leaf: the strict cardinal bound on non-full filtered subcategories and the regrouping comparison are not provided by the searched declarations.
- `citations.json`: one verbatim statement quotation for each cited node in each proof step; auxiliary delivery evidence.
- `report.md`: this report. The sandbox also retains the earlier `searches.jsonl` and the reproducible local writing script; neither changes the shared repository.

New nodes: 0. New Mathlib leaves: 0. All three proof dependencies already exist: `def-weil-pbc-category-colimit`, `def-weil-size-convention`, and `lem-coef-infinite-cardinal-square-power`.

## Attachments

None. Searches under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint id, cardinal regrouping, filtered subcategory and related terminology found no declaration stating every clause. The upstream master reference was also searched for the exact id. No project theorem was inferred from a Mathlib theorem, and no sorry declaration was accepted as a proof.

## WANTED

WANTED: Lurie, Higher Algebra, proof of Theorem B.0.20, printed pp. 1485–1487, for lem-coef-filtered-colimit-cardinal-regrouping; the online PDF was read for context but is not locally archived under literature/. No download was made. The source already describes this item as an agent refinement, rather than a named HA theorem; the delivered proof is marked `proof_origin.by = agent` and uses the locally available definitions and an existing Mathlib arithmetic leaf.

## Audit and changes

The interruption left only search logs and brief markers in the sandbox: there was no node, report, citations file or running delivery process to resume. I read and reused all eight earlier logged searches, then ran one additional recorded grep to locate the exact fiberwise-colimit declarations. I retained the item's inherited search records and appended the actual sandbox log entries, preserving query text, timestamps and result summaries. Loogle's unknown-identifier response for `CategoryTheory.Subcategory` is recorded as unavailable, not as proof of absence.

The item was still unsplit in the current shared DAG. Its statement is true as written, and no STATEMENT-DISPUTED correction is needed. Its empty proof omitted the closure construction and the actual canonical comparison. Step 4 of its parent `lem-coef-categorical-pattern-model-calculus` needs precisely the retained assertion. I read that parent step, the blueprint ancestor `prop-coef-integral-exceptional-adjoint` (second proof paragraph, finite-coefficient mapping-complex infrastructure), the chapter and unit records, GOAL.md and coord/dag-sync.md. This is an auxiliary ordinary-category argument below the unit route. No chapter, unit, blueprint ancestry, target or maintainer-owned metadata is changed.

I searched the whole DAG by filtered-subcategory, finite-word/cardinality, regular-cardinal and colimit-assembly terminology, and searched the blueprint using `blueprint_refs.py ancestor` and `search` (filtered colimit cardinal regrouping; filtered subcategor; finite sequences; bounded filtered; regroup). There is no imported blueprint node stating this item in another form, so `blueprint.same_as` remains empty. These searches located the existing square-cardinal leaf, which replaces any need for a new arithmetic node. The existing `lem-coef-small-directed-superset` is a theorem for subsets of posets under a different cofinal-family hypothesis, not a result about arbitrary non-full subcategories. The existing `lem-coef-directed-cover-colimit-assembly` and `lem-coef-colimit-subdiagram-approximation` concern coherent diagrams in infinity categories; this proof uses only ordinary colimit universal properties. None is silently applied across coefficient/category conventions.

Mathlib candidates were read in the pinned source. `CategoryTheory.IsFiltered.filteredClosure` and `small_fullSubcategory_filteredClosure` in Filtered/Small.lean:33–105 use a full subcategory and a universe bound, not the necessary strict bound on its arrows. `colimitUncurryIsoColimitCompColim` in Limits/Fubini.lean:510 treats a product of two fixed indexing categories. The variable fiber construction and `isColimitCoconeFiberwiseColimitOfCocone`/`colimitFiberwiseColimitIso` in Limits/Shapes/Grothendieck.lean:54–79,136–146,200–202 do not identify the total Grothendieck diagram with the original J diagram. None states the complete item or specializes to it in one line. Cardinal-filteredness definitions and directed reindexing results also do not supply its cover. Thus neither an attachment nor a Mathlib leaf is claimed.

## Not duplicates

No new node is created, so there are no new/existing tag pairs to distinguish. The arithmetic and colimit definitions are reused directly.

## Review by NF

I read the complete item statement, the statements of all three cited nodes, and the local source `literature/stacks-project/categories.tex`, labels `definition-directed` (002V) and `definition-colimit` (002F), including the universal-property uniqueness paragraph. I checked `Cardinal.mul_eq_self` at Mathlib/SetTheory/Cardinal/Arithmetic.lean:45 against the existing leaf. I also read the HA B.0.20 proof context online: it supplies the model-category accessibility context, not this exact bounded-cover lemma. The proof therefore does not pretend that either Stacks definition or HA states the whole theorem. Every displayed argument below is written into the item, with the arithmetic theorem as a cited node. There are no new statement-only nodes to audit.

Step 1 uses exactly the three filteredness clauses from `def-weil-pbc-category-colimit`: nonemptiness chooses j0; two-object cocones supply two arrows for each object pair; equalizing parallel arrows supplies h. The chosen witnesses need not be universal coequalizers. I explicitly retain arrow sets rather than full subcategories, so no uncontrolled Hom set is introduced. At this stage E_n need not itself be a subcategory; the union is checked later.

Step 2 uses only the square identity from `lem-coef-infinite-cardinal-square-power`, whose statement really gives theta times theta equals theta for an infinite small cardinal. Theta=max(aleph0,|E_n|) meets that hypothesis and is strictly less than lambda because lambda is uncountable. Endpoint sets, pair sets and the finite collection of witness families are bounded explicitly. Induction gives |E_n|<lambda and regularity in the item's own hypotheses bounds the countable union. This is where uncountability and regularity are used; no cardinal bound on full Hom sets is assumed. The count is part of the actual closure construction and conceals no separate comparison theorem.

Step 3 again uses the filteredness definition from `def-weil-pbc-category-colimit`. Every finite selection of arrows appears in a common stage, so identity/composition closure and both witness conditions really hold in the union. The inherited category laws are equations in J. I wrote the reduction of a finite diagram to the two filteredness clauses explicitly: common target for its objects, followed by finitely many parallel-pair equalizations, postcomposing every leg. Thus the item's finite-diagram convention, including its empty diagram, is respected. This is an elementary verification of the constructed object, not a cited definition used in place of a missing theorem.

Step 4 uses `def-weil-size-convention` only for the Grothendieck-universe convention. Subcategories are subsets of the two small underlying sets, so their collection and its indicated subset P_J are small by the power-set closure of a universe. The union of fewer than lambda bounded arrow sets is bounded by the regularity hypothesis already in the item; applying the explicit construction in steps 1–3 gives an upper bound. Each old object's identity ensures inclusion of objects, not just arrows. The empty family uses the empty-seed construction. I verified that this gives precisely lambda-directedness and smallness, not just ordinary filteredness.

Steps 5 and 6 use the actual universal property in `def-weil-pbc-category-colimit`. It gives the transition map and its coprojection equation, and uniqueness gives its identity/composition equations. All inner, outer and J colimits exist by the item's cocompleteness hypothesis; every indexing category was proved small first. Restricting the J-colimit cocone gives q_K and then the canonical q, with its equations explicitly stated. No Fubini or final-functor theorem is being cited just for its name.

Step 7 uses the same colimit universal property after checking a cocone: two choices of K containing j are compared in a common upper bound R, and the coprojection equations show equality. Every arrow f lies in a member, allowing the cocone equation to be checked there. No full-subcategory assumption is used. This produces r from that actual cocone, rather than an unspecified isomorphism.

Step 8 uses uniqueness in the same cited definition three times: on J to show qr=1, on each K to show rqk_K=k_K, and on P_J to show rq=1. I checked all domains and composition directions. In particular q is exactly the map demanded by the statement, since qk_Ki_{K,j}=a_j. The proof works in any ordinary locally small cocomplete category and never invokes Yoneda, coherent colimits, or a large category of all diagrams.

I tested the empty seed in a nonempty filtered category, a terminal category, a finite filtered category, and J=omega. The closure may be countably infinite even for a finite seed; this confirms the need for uncountable lambda. The empty category J is excluded by the stated filteredness hypothesis, so it is not an unaddressed case. If J already has fewer than lambda arrows it belongs to P_J, and the comparison specializes to the terminal-index case. For a category with two objects a,b, arbitrarily many parallel arrows a to b, and a terminal object t equalizing them, a small witness subcategory can retain selected arrows and the maps to t; the full subcategory can have at least lambda arrows. This verifies why replacing the construction by Mathlib's full closure would fail. Constant and zero/initial-object valued diagrams satisfy the same inverse equations without extra assumptions.

I checked delivery-errors B–E against the written files: there are no new nodes, no restated-clause auxiliary lemmas, no altered statements, no circular appeals, no off-unit proof tools, and no unrecorded literature theorem hidden behind a definition citation. All node references are copied in citations.json as verbatim pieces of their statements. All eight proof steps are below 2000 characters (maximum 1009), and none hides a separately used standard comparison or identification; the full canonical-map argument is present. No SGA source is used. No Lean, compiler, Lake, live repository or launcher file was written or run.

## Unfinished work

None in the requested one-level split. The required server dry run and direct delivery follow this report; the delivery tool output is the authority for their outcome.
