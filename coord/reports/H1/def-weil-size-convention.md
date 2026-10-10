Files written:

- `dag/nodes/sec-picard-framework/def-weil-size-convention.json`: definition, split; no new nodes and no Mathlib leaf.

Attachments: none. No sorry-free declaration in `WeilConjectures/` states the convention, and no matching blueprint node exists elsewhere in the repository.

WANTED: none.

The imported node is a standalone foundational convention. It introduces the two Grothendieck universes and specifies the skeleton and derived-category/filtered-colimit size choices, so there are no subordinate proof lemmas to create. Its statement dependency is the existing scheme definition, which supplies the principal objects said to be under consideration; the coefficient rings are arbitrary ambient data in the convention and do not require a separate theorem node. The blueprint source path recorded in the node is not present in this checkout; the node statement itself is the available imported blueprint text. The Mathlib searches found only general essential-smallness and derived-category declarations, not this convention.

## Review by H1

I read the item node, its chapter and unit records, and the cited `def-pc-scheme` statement. I searched both `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `/home/ubuntu/weil-conjectures-slopmaster2/WeilConjectures` for `def-weil-size-convention`, universe terminology, and skeleton terminology. No declaration or docstring tag was found, so there is no Lean attachment. I also searched the repository blueprint index; no other blueprint node states the same convention. The statement has no proof steps whose citations would need checking. The recorded LeanFinder, Loogle, Mathlib grep, and unavailable LeanSearch searches were run with `msearch.py`; their results do not provide an exact Mathlib definition. I changed only the stage-1 metadata: `status` is now `split`, `stmt_deps` names the existing scheme definition, `blueprint.same_as` is `[]`, the searches are recorded, and the split report explains why no child nodes or citations are present.

## Second reading by H1

- Item statement: checked against the imported blueprint node text at `source.place` (order 661); the two universes, bounded skeleton replacement, and formation of derived categories and filtered colimits in `\mathcal V` agree. The existing `def-pc-scheme` dependency supplies the scheme notion; coefficient rings are parameters of the convention. Zero objects, fields, empty schemes, and degree values `n=0,1` are inapplicable because this is a size convention, not a theorem indexed by such data.
- Proof steps: none; the definition fixes data and has no argument or cited proof facts, so `citations.json` is correctly empty.
- New nodes: none; B1--B7 are vacuous. No duplicate or Mathlib child was introduced. The repository blueprint search found only this item and its two users, and the four recorded `msearch.py` searches found no exact Mathlib convention (LeanSearch was recorded as unavailable).
- Changes made in this second reading: none to the statement or node set; verified the worker's `split` status, `stmt_deps`, `blueprint.same_as = []`, empty citations, and report review section. The review section above remains in place.
