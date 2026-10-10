# Stage-1 report: def-sp-abelian

## Files written

- `def-sp-abelian.json`: Mathlib leaf; no new nodes.

## Attachments

None. No sorry-free project declaration tagged `(blueprint: def-sp-abelian)` was found in `WeilConjectures/`.

## WANTED

None.

## Review by E1

I read the item node, the chapter and unit records, the stage-1 worker brief, and the delivery-error checklist. The item is the imported definition at order 497 and has no proof steps or hidden hypotheses. I searched the whole supplied `WeilConjectures/` source for the item id, its blueprint tag, and the abelian-category terminology; the source uses Mathlib's `CategoryTheory.Abelian` class but contains no project declaration for this item. I then read `Mathlib/CategoryTheory/Abelian/Basic.lean`: its class at line 112 requires a preadditive category, finite products, kernels, cokernels, and normal monos and epis; the same file explains that finite products give a zero object (lines 107-109) and derives finite biproducts and a zero-object instance (lines 274-284). Thus its definition specializes to the node's formulation in one line, with normal mono/epi exactly expressing the kernel/cokernel clauses. I ran the required LeanFinder, Loogle, grep, and LeanSearch searches, recorded their outputs and the unavailable LeanSearch service in `mathlib_searches`, and checked the blueprint/DAG for duplicates. Since this is a definition leaf, there are no proof-step citations and `citations.json` is empty. Small cases (the zero category and the category of abelian groups) satisfy both formulations.

## What was wrong or corrected

The imported node was unsplit with no Mathlib search record. I filled `blueprint.same_as` with `[]`, recorded the Mathlib match and searches, and marked the item as a Mathlib leaf. No statement correction was needed.

## What could not be finished

Nothing. The msearch LeanSearch endpoint was unavailable; this is recorded explicitly, while the LeanFinder, Loogle, and source inspection establish the match.

## Second reading by E1

- Item statement: checked against the imported blueprint definition at order 497 and Mathlib `CategoryTheory.Abelian` in `Mathlib/CategoryTheory/Abelian/Basic.lean` (line 112); all structural hypotheses agree, including the derived zero object and finite biproducts (lines 107–109 and 274–284).
- New node `def-sp-abelian`: checked as a statement-only Mathlib leaf; it is self-contained, has its definition dependency, records the declaration/file/line and searches, and has no proof steps or citations requiring review.
- Proof steps: none exist for this definition leaf.
- Edge cases: the zero category and the category of abelian groups satisfy the stated structure; no field, scheme, or numerical parameter occurs.

No changes were needed after the second reading. The dry-run delivery validator passed; the unavailable LeanSearch service remains recorded in `mathlib_searches` and `searches.jsonl`.
