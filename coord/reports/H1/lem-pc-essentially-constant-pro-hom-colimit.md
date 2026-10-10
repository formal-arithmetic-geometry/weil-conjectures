1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-essentially-constant-pro-hom-colimit.json` (item, split).
- No new nodes (the attempted auxiliary node was rejected by the dry run as a clause-level restatement).

2. Attachments: none. No sorry-free declaration in `WeilConjectures/` states the item.

3. WANTED: none; `literature/stacks-project/categories.tex` is available in the project literature checkout used for this split.

4. The item was unsplit and had no proof. I retained its statement and wrote the cone construction, surjectivity, and injectivity arguments directly as three steps. The attempted auxiliary node was removed because the dry run identified it as a clause-level restatement (D1/D2). The existing inverse-system definition is abelian-group-specific and is not used.

## Review by H1

I read the item's source as the sixth equality in Derived Categories Lemma Tag 0FND and the underlying characterization in Categories Lemma Tag 05PZ. Step 1 defines the map from cone compatibility; step 2 uses the retraction for surjectivity; step 3 uses cofiltered refinements and eventual factorization for injectivity. The dry run confirmed that no auxiliary clause node is permitted. Small cases checked: a constant diagram gives the identity map, and an initial value gives singleton Hom sets.

## Second reading by H1

- Item statement: checked against Categories Lemma Tag 05PZ (label `categories-lemma-characterize-essentially-constant-pro`) and the sixth equality of Derived Categories Tag 0FND; the cofiltered index, category, essentially constant pro-object, value $X$, arbitrary target $Y$, and Hom-colimit bijection agree hypothesis by hypothesis.
- Step 1: checked against Tag 05PZ conditions (1)--(4); verdict: the cone maps, retraction equation, transition compatibility, and representative map are now stated explicitly, with no stale node citation.
- Step 2: checked against Tag 05PZ condition (4); verdict: the representative $h\\circ r$ and calculation using $r\\circ u_{j_0}=\\operatorname{id}_X$ give surjectivity directly.
- Step 3: checked against Tag 05PZ's injectivity calculation; verdict: common cofiltered refinement and the further transition through the cone are written as actual composites, so no “same argument” or unsupported transport remains.
- New nodes: none; the attempted auxiliary factorization node would restate a clause of the item and was correctly omitted.
- Definitions and source: the only cited definition node is `def-weil-abstract-derived-category`; source labels and TeX were checked against the local Categories and Derived Categories files, with Mathlib searches retained from the worker.
- Edge cases: constant diagrams give the identity map; a zero object or field gives the expected Hom bijection; the empty scheme has no effect because the statement is categorical; the first indices $0$ and $1$ have no special behavior because no numerical parameter occurs.

Changes made: removed the invalid citation to nonexistent node `lem-pc-pro-hom-colimit-factorization`, rewrote all three proof steps with explicit cone/refinement composites, and added this independent second-reading record.
