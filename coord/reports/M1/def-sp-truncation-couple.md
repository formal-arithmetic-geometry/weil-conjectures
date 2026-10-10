Files written:

- `dag/nodes/sec-abelian-varieties/def-sp-truncation-couple.json`: definition, no new child nodes; Mathlib searches found no exact match.
- `citations.json`: empty because the item is a definition and has no proof steps.

Attachments: none.

WANTED: none.

The item is an imported definition rather than a theorem. I checked its statement against the blueprint node `def-sp-truncation-couple`, order 520, and retained all four existing statement dependencies. The definition introduces the truncation couple from the canonical truncation triangles, applies the K-injective derived functor to bounded-below complexes, and records the three bidegrees; these are all part of the definition itself, so splitting any displayed clause into a child node would merely restate the item. I searched the DAG and blueprint for truncation-couple statements and found only this node plus downstream applications and the distinct etale truncation definition. The Lean source under `WeilConjectures/` contains no declaration tagged `(blueprint: def-sp-truncation-couple)` and no declaration with the exact construction.

## Review by M1

I read the item JSON, its blueprint source metadata, the unit record `sk-prop-av-pqf-finite`, and the dependent definitions `def-sp-left-exact-additive`, `def-sp-grothendieck-abelian`, `def-sp-kinjective-bridge`, and `def-sp-exact-couple`. Each cited dependency supplies the notion used at the corresponding point of the statement. The hypotheses on `v`, the Grothendieck categories, bounded-below `K`, and vanishing below `a` are explicit in the item. The displayed objects `D` and `E`, truncation triangle, derived-functor construction, and structure-map bidegrees are definition clauses, not independent lemmas. I therefore corrected only the stage metadata (`status`, `blueprint.same_as`, and `split_report`) and created no node. The Mathlib searches were run for the item: LeanFinder returned only generic `ComplexShape.Embedding.truncLE/GEFunctor` declarations, Loogle returned no usable match, grep returned no `truncation couple` declaration, and LeanSearch was unavailable; none states this project-specific construction.

What could not be finished: no Lean attachment exists, so the item remains a natural-language definition for later formalization.

## Second reading by M1

- Item statement: checked against the blueprint source `def-sp-truncation-couple.md` (node order 520), the four cited definition nodes, and the downstream truncation-couple uses; verdict: the categories, functor, bounded-below complex, vanishing range, truncation triangles, derived-functor construction, and all three bidegrees agree hypothesis by hypothesis. The source is an imported blueprint definition and names no Stacks tag.
- Proof steps: none; this is a definition node with an empty proof, so there are no dependency or citation steps to audit.
- New nodes: none; the displayed clauses are the definition itself, and splitting any one out would restate the item. The blueprint search found no smaller duplicate node.
- Edge cases: checked the zero complex, a complex concentrated in one degree (including a field-valued object), the empty/zero category interpretation, and `a = 0` or `a = 1`; the construction and indexing remain well-typed and no clause becomes false.
- Metadata and form: checked statement-only form, single TeX rendering, self-contained definition references, imported-node `blueprint.from = null`, empty citations, and the recorded Mathlib search log; verdict: compliant.

Changes made: none. The independent reading found no mathematical, duplication, citation, or delivery-contract defect.
