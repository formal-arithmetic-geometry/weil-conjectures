1. Files written:

   - `def-sp-left-exact-additive.json`: definition, no new subordinate nodes, not a Mathlib leaf.

2. Attachments: none.

3. WANTED: none.

4. No statement or blueprint error was found. The item is a definition rather than a theorem: the additivity, left exactness, and right-derived-functor construction are introduced directly. The existing node `lem-sp-derived-well-defined` is the named deferred result for independence of the injective resolution and the identification in degree zero, so those claims were not turned into proof steps here.

5. Nothing remains unfinished.

## Review by G1

I read the item node and its blueprint metadata (order 501), then read `def-sp-abelian` and `def-sp-injective-resolutions`, the two statement dependencies named by the item. The former supplies the abelian-category setting and the latter supplies the meaning of an injective resolution; both are used by the statement exactly where cited. I also read `lem-sp-derived-well-defined`: it explicitly takes a left exact additive functor and an injective resolution as inputs and proves the two deferred well-definedness claims, so the definition need not duplicate that theorem. I searched the slopmaster2 source for the blueprint tag and for right-derived/left-exact declarations; there is no project declaration stating this item. The Mathlib searches found only general additive/left-exact infrastructure, not this project definition, so no Mathlib attachment or new node is appropriate. Since the item has no proof steps, `citations.json` is the empty list.

## Second reading by G1

- Item statement: checked against blueprint node `def-sp-left-exact-additive` (order 501), including the abelian-category, additivity, left-exactness, enough-injectives, and injective-resolution clauses; verdict: agrees hypothesis by hypothesis.
- Proof steps: none; the displayed construction is definition text and well-definedness is explicitly deferred to `lem-sp-derived-well-defined`; verdict: no uncited proof claim.
- New nodes: none; B1-B7 and duplicate-node checks are vacuous.
- Edge cases: the zero object and an injective object give the expected degree-zero construction; the empty/zero category and a field-valued module category introduce no contradiction; verdict: consistent.
- Mathlib/slopmaster2 search records were read from `searches.jsonl`; they find only general additive/left-exact infrastructure and no exact project definition, so no attachment is made.
- Kept the imported item's `blueprint.from` as `null`, as required for a blueprint node; no mathematical text or maintainer metadata was changed.
- The existing dependency `def-sp-injective-resolutions` uses the phrase “with enough injectives” without defining that phrase; this is a pre-existing DAG issue (also recorded in that node's lead note), not a defect introduced by this split.
