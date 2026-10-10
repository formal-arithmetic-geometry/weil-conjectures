Files written:

- `dag/nodes/sec-nagata-compactification/lemma-nagata-filtered-colimit-finite-data.json`: item, statement, no new nodes, Mathlib searches recorded (no exact Mathlib match).
- `citations.json`: citation for the item's one proof step.

Attachments: none.

WANTED: none.

The item is a blueprint-only bookkeeping lemma and is explicitly marked bypassed by the blueprint. I found no declaration carrying its blueprint tag or equivalent statement in `WeilConjectures/` or `Comparator/`. The existing dependency `lemma-nagata-directed-finite-upper-bound` is the only non-elementary input; no duplicate or auxiliary node was created.

## Review by C1

I read the imported item node, its blueprint proof paragraph (order 331), the unit record `sk-prop-nagata-sketch-approximation`, and the existing dependency node `lemma-nagata-directed-finite-upper-bound`. I also searched the project Lean source for the item tag and for filtered-colimit finite-data terminology; no project declaration states the item. The proof step follows the blueprint: representatives for finitely many elements are placed at one common stage using the cited upper-bound statement, each equality is witnessed at a later stage, a second finite upper bound combines the finitely many witnesses, and ring maps preserve the resulting equalities. The citation quote is copied verbatim from the dependency statement and supplies exactly the common-upper-bound fact used by the step. I checked that the selected finite sets and the later-stage propagation are covered by the hypotheses in the item, and that the proof dependency is exactly the union of the step's uses. Mathlib searches used LeanFinder, Loogle, grep, and the unavailable LeanSearch service; the returned declarations were generic filtered-colimit or finite-presentation facts and did not state this arbitrary finite-ring-data lemma.

No corrections to the mathematical statement were needed. The blueprint status note explains why the formal Lean route bypasses this bookkeeping, but it does not provide a project declaration for attachment, so the item is recorded as split rather than attached.

## Second reading by C1

- Item statement: checked against the imported blueprint node at order 331 and its unit record; the directed-system, finite-elements, finite-equalities, and persistence clauses are retained, with no Stacks tag supplied by this blueprint-only source.
- Step 1: checked each use against `lemma-nagata-directed-finite-upper-bound` and `lem-pc-filtered-colimit-commrings-elementwise`; representative existence and eventual equality are now cited, the two finite upper-bound applications are explicit, and persistence under ring maps is elementary.
- New nodes: none; the split creates no auxiliary node, and the existing elementwise filtered-colimit result is an exact Mathlib-backed statement.
- Mathlib leaf: checked `lem-pc-filtered-colimit-commrings-elementwise` and its recorded `Concrete.isColimit_exists_rep` / `Concrete.isColimit_rep_eq_iff_exists` declarations and lines; it supplies both clauses used by step 1.

Changes made: added the missing filtered-colimit citation and expanded step 1 to state the representative, equality-witness, finite-upper-bound, and persistence arguments; set `blueprint.same_as` to the searched empty list; expanded the split report and citations accordingly.
