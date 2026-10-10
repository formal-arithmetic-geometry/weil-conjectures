1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-cone-pseudo-coherent.json`: statement, no new Mathlib leaf.
- `citations.json`: one verbatim citation for the proof step.

2. Attachments:

- `lem-pc-ring-pseudo-coherent-distinguished-triangle` contains the item's exact first clause; no Lean declaration attachment was found.

3. WANTED:

None. The Stacks TeX source was checked at `more-algebra.tex`, Tag 064R (`lemma-cone-pseudo-coherent`); the imported repository path is the same source citation.

4. What was wrong in the node or earlier work:

The imported item cited `def-pc-derived-category`, which defines the scheme-level derived category of sheaves and does not define `D(R)` for a ring. I changed the statement and `stmt_deps` to cite `def-weil-abstract-derived-category`, matching the ring-level node already used for Tag 064R. The item was otherwise a duplicate specialization of `lem-pc-ring-pseudo-coherent-distinguished-triangle`; creating another helper node would have duplicated that result.

## Not duplicates

`lem-sc-cone-pseudo-coherent` vs `lem-pc-ring-pseudo-coherent-distinguished-triangle`: the existing node states all three two-out-of-three clauses for a distinguished triangle in `D(R)`, while this item records only the first clause with the names `K`, `L`, and `M`; the item is therefore proved by that broader statement rather than a new node.

## Review by F1

I read the item source citation (Stacks Tag 064R, `lemma-cone-pseudo-coherent`) and compared every hypothesis with the existing node `lem-pc-ring-pseudo-coherent-distinguished-triangle`. Its statement introduces the same ring `R`, integer `m`, derived category `D(R)`, bounded finite-free witness, cohomology isomorphisms above `m`, degree-`m` surjection, distinguished triangle, and hypotheses that the first and second objects are `(m+1)`- and `m`-pseudo-coherent. The quoted clause in `citations.json` is copied verbatim from that node and directly supplies the conclusion. I checked the dependency correction against `def-pc-derived-category`: that definition is for sheaves on a scheme, so it cannot define the ring-derived category used here; `def-weil-abstract-derived-category` is the dependency named by the broader 064R node. I searched the DAG by the Tag 064R label and pseudo-coherence keywords and found the broader node, so no new node was created. The Mathlib searches were rerun for this item: LeanFinder returned only mapping-cone infrastructure, Loogle rejected the unknown pseudo-coherence identifier, grep returned only incidental cohomology documentation, and LeanSearch was unavailable; none states the item.

## Second reading by F1

- Item statement: checked against More on Algebra, Tag 064R (`lemma-cone-pseudo-coherent`), including the ring, integer, derived category, witness, triangle, and two hypotheses; verdict: exact first clause.
- Step 1: checked against the complete statement of `lem-pc-ring-pseudo-coherent-distinguished-triangle`; its first clause has the same hypotheses and conclusion after renaming `A,B,C` to `K,L,M`; verdict: valid direct application, with the citation quote verbatim.
- New nodes: none; the split creates no helper node, so B1--B7 and duplicate checks reduce to the existing ring-level node search.
- Edge cases: the zero object has the zero bounded finite-free witness; the statement is valid over a field and for every integer `m`; no scheme or empty-scheme hypothesis is present or needed.
- Dependency: replaced the stale `def-pc-derived-category` reference with `def-weil-abstract-derived-category`, which defines the ring-derived category used by `D(R)`.
- Source availability: the source was read at `/home/ubuntu/c1-stacks-review/more-algebra.tex`, lines 15910--15958; the earlier report's claim that the TeX was unavailable was corrected.
- Mathlib search records: the existing recorded LeanFinder, Loogle, grep, and unavailable LeanSearch results were checked against `searches.jsonl`; no Mathlib declaration states pseudo-coherence in a distinguished triangle.
- Delivery dry run: `deliver.py F1 lem-sc-cone-pseudo-coherent --no-push` passed preflight.
