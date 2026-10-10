1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-derived-direct-image-direct-sums.json`: statement, duplicate attachment, no new node; Mathlib searches found no matching derived pushforward theorem.
- `citations.json`: one verbatim citation for the duplicate theorem.

2. Attachments:

- `lem-pc-derived-direct-image-preserves-direct-sums` is the existing DAG node stating this item exactly.

3. WANTED:

None. The item is covered by the existing Stacks source reference Tag 08DZ already recorded in the DAG.

4. What was wrong in the node or blueprint:

The imported item was a duplicate of `lem-pc-derived-direct-image-preserves-direct-sums`. Both state that for a quasi-compact, quasi-separated morphism of schemes, derived pushforward on quasi-coherent derived categories commutes with all set-indexed direct sums. I changed the item from unsplit to split and cited the existing node; no new node was created. The item's blueprint route is from `lem-pc-projection-formula`, where this theorem is used as the direct-sum input.

## Not duplicates

`lem-pc-derived-direct-image-direct-sums` vs `lem-pc-derived-direct-image-preserves-direct-sums`: the statements have the same hypotheses, objects, and conclusion; the present item spells out the canonical comparison map while the existing node expresses the equivalent functorial preservation property.

5. What I could not finish, and why:

Nothing. The Lean source contains no sorry-free project declaration tagged with this item, so the attachment is to the existing DAG theorem rather than to Lean.

## Review by M1

I read the item node and its source citation, Stacks Project `perfect.tex`, Section 36.4, Lemma 36.4.5, Tag 08DZ. I also opened the full existing node `lem-pc-derived-direct-image-preserves-direct-sums` and checked its statement hypothesis by hypothesis: it assumes a quasi-compact, quasi-separated morphism of schemes, takes arbitrary set-indexed families in `D_QCoh`, and asserts that the canonical direct-sum comparison for `Rf_*` is an isomorphism. This is exactly what the present item asks for, so the only proof step cites that statement and no hidden proof details.

The citation quote is copied verbatim from the existing node. I searched the whole DAG and blueprint for the theorem and found the existing node; therefore no new node was needed and there are no duplicate dependencies to introduce. I ran LeanFinder, Loogle, grep, and LeanSearch searches for a Mathlib theorem. The first three produced only underived pushforward APIs or no hits; LeanSearch was unavailable and is recorded as such. I tested the edge cases conceptually: an empty family gives the zero comparison, and a singleton family gives the identity comparison, both covered by the existing all-set-indexed statement.

## Second reading by M1

- Item statement: checked against Stacks `perfect.tex`, Tag 08DZ, Lemma 36.4.5; the quasi-compact and quasi-separated hypotheses, arbitrary set-indexed family in `D_QCoh`, and canonical comparison-map isomorphism all agree.
- Step 1: checked against the statement of `lem-pc-derived-direct-image-preserves-direct-sums`; its functorial preservation of all set-indexed direct sums is exactly the comparison-map assertion used here, with no proof details imported. Verdict: correct.
- New nodes: none; the whole DAG search found `lem-pc-derived-direct-image-preserves-direct-sums` as the existing theorem, so no new statement requires B1-B7 or an independent Mathlib leaf review.
- Citation: checked `citations.json` against the existing node statement verbatim; the quoted sentence contains the complete fact used by Step 1.
- Edge cases: the empty family reduces to the zero comparison and a singleton family to the identity comparison; both are included by the existing all-set-indexed statement. No hypothesis is added or dropped.

Changes made: retained the duplicate attachment and did not add a redundant node; added this second-reading record to document the source, dependency, duplicate search, citation, and edge-case checks.
