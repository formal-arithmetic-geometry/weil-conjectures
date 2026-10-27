# Stage-1 report: lem-sfb-scheme-size-open-cover-bound

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-scheme-size-open-cover-bound.json`: statement, now split by reuse of an existing identical statement; no Mathlib match.
- `citations.json`: the verbatim statement excerpt for the sole proof-step citation.
- `report.md`: this report.

No new nodes; no Mathlib leaves. All repository and Lean files were read only.

## Attachments

None. Searches under `lean/WeilConjectures/` for the blueprint id, scheme-size names and affine-open cardinal estimates found no project declaration of the full statement. General cardinal-generation lemmas and unrelated affine-cover constructions are not attachments.

## WANTED

None. The Stacks source and current latest blueprint are available locally.

## Existing duplicate and route

`lem-sfb-open-cover-scheme-size` already states the exact estimate, including the explicit aleph-zero term and the empty covering. Its only dependency is `def-pc-scheme`; its current status is unsplit. I read its whole statement, not a proof, and use it as the shared existing prerequisite. This item is a forwarding split: it does not claim that prerequisite is already proved, and creates no new copy of the item's conclusion. This is the existing-node reuse required by stages/1-dag.md section 3 and the brief's duplicate rule. Both nodes lie in `sec-six-functors-basics`, unit `sk-thm-sf-ctf-stability`. The candidate's dependency closure does not contain this item, so the edge is acyclic.

Whole-DAG searches for 000Q, scheme size and affine-open cardinality exposed this duplicate and the distinct size estimates `lem-sfb-affine-scheme-size` and `lem-sfb-qc-lft-scheme-size-bound`. Whole-blueprint searches with `tools/blueprint_refs.py search 'scheme size'` and `search '000Q'` each returned zero imported blueprint matches. The ancestor command returned None, matching this item's existing blueprint.from.node. That maintainer-owned field is preserved. I read the current latest unit and its direct-images proof (3), and the DAG chapter and unit records; this supporting set-theoretic estimate is below that route, not a replacement for it.

## Not duplicates

No new nodes are proposed. The already existing pair `lem-sfb-scheme-size-open-cover-bound` and `lem-sfb-open-cover-scheme-size` is an exact duplicate, and this delivery deliberately reuses the latter without editing or duplicating it. A later maintainer merge of the ids is possible but outside this worker's permitted edits.

## Source error

Stacks `sets.tex`, Tag 000Q (`lemma-bound-size`), prints the maximum without an explicit aleph-zero term. For the empty covering of the empty scheme that right-hand side is zero, whereas the preceding definition gives s(empty) = aleph-zero. This was already repaired in both existing DAG statements. I retained the item's statement byte for byte. Thus there is no new STATEMENT-DISPUTED correction to the imported item. A nonempty family of empty opens also satisfies the repaired formula.

## Mathlib searches

I read the five earlier search records already in the live item and retained them. I additionally ran the required logged msearch.py queries under Q120 for this item: grep, Loogle, LeanSearch, and LeanFinder with two phrasings. All services answered successfully. The hits describe affine covers and their indices, open-cover constructions and compact-open refinements; none states the cardinal maximum for all affine opens and their section rings. The exact query strings and returned summaries are appended to mathlib_searches and retained in searches.jsonl. No Mathlib leaf or unrun search is claimed.

## Review by Q120

I read Stacks `sets.tex`, section-categories-schemes (the definition of size), Tag 000P (`lemma-bound-affine`) and Tag 000Q (`lemma-bound-size`) with their proofs. In particular, 000Q refines each affine open by finitely many affine opens inside the cover members, bounds sections by injection into their finite product, and counts finite families of such opens. It does not require intersections of arbitrary affine opens of X to be affine, nor does it require X or the cover members to be quasi-separated. The present delivery uses the existing node for precisely this theorem rather than concealing this argument inside a newly created restatement. There are no new-node sources to check.

For step 1 I opened `lem-sfb-open-cover-scheme-size.json` and compared every clause: its Y is our X, its open Y_i are exactly the induced U_i, the indexing set is unrestricted, and its definition of s counts the same affine opens and section rings. Its conclusion is literally the required maximum after renaming; citations.json copies that sentence verbatim. Its final sentence explicitly allows the empty covering. It imposes no quasi-compactness, quasi-separatedness, nonemptiness, separatedness or finiteness condition. All its hypotheses are therefore supplied by the item. The sentence about the empty supremum uses the convention already specified in the item, not an additional theorem. There are no other proof-step citations or hidden non-elementary steps.

I checked B through E of delivery-errors.md point by point. B: there are no new node statements or notions to introduce, no fabricated search records, and the exact TeX and blueprint fields are preserved. C: the one cited node states the theorem used and its dependency closure is acyclic; it is in the same unit. D: no new node restates the item or moves its proof elsewhere; the only reduction reuses a duplicate that was already in the live DAG, as the duplicate rule instructs. E: the hypotheses match exactly. Small cases checked were the empty index set and empty scheme (both sides aleph-zero), a nonempty family of empty opens, the singleton cover U=X, and an infinite disjoint union of spectra of finite fields (the index-cardinality term is necessary). The lack of quasi-separatedness is harmless because the existing theorem and its source have no such hypothesis. No proof step is longer than 2000 characters.

The only correction needed was to replace the empty proof with the explicit existing-node application. The original statement, source and maintainer-owned metadata were retained.

## Unfinished work

None for this one-level split. The pre-existing prerequisite remains independently unsplit; proving it is not claimed by this forwarding delivery.
