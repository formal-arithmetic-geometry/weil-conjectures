# Stage 1 delivery: `lem-weil-pbc-field-point-factors-through-immersion`

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-field-point-factors-through-immersion.json` — existing node split into four proof steps; its statement is unchanged and its status is `split`.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-closed-immersion-residue-field-iso.json` — new public unsplit statement node for the residue-field isomorphism of a closed immersion.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-field-point-factors-through-closed-immersion.json` — new public unsplit statement node for factoring a field-valued point through a closed immersion.
- `coord/reports/C1/lem-weil-pbc-field-point-factors-through-immersion.md` — this report and review.

## Attachments

None. This Stage 1 delivery writes no Lean code, module, or private proof lemma.

## What was wrong or incomplete

The imported item was unsplit with an empty proof. I retained its statement and route, then made the factorization argument explicit. The first two steps factor an immersion as a closed immersion followed by an open immersion and compose the two residue-field maps. The third step restricts the field-valued point to the intermediate open subscheme and applies the new closed-immersion factorization statement. The fourth step proves uniqueness using monomorphism of the open immersion and the uniqueness in the closed-immersion statement, and records the geometric-point specialization. The two facts needed for the closed part are now public statement-only nodes with `created.item` exactly equal to this item; each records LeanSearch, LeanFinder/Loogle, and Mathlib-source grep searches.

## What could not be finished

No Lean declaration was found or attached, and no Lean file was written or compiled, as required for Stage 1. The new reusable nodes remain `unsplit` and therefore enter the Stage 1 queue.

## Review by C1

I independently checked the unchanged statement against Stacks `schemes.tex`: Definition 01IO gives the closed-then-open factorization of an immersion; Definition 01HK supplies the surjective local-ring map for a closed immersion; the discussion before Lemma 01J9 identifies field-valued points and residue-field maps; Lemmas 01HI and 01L7 give the open-subscheme restriction and monomorphism properties; and Lemma 0356 gives factorization from a reduced source through a closed subscheme when the image is set-theoretically contained in it. Step 1 uses the cited naturality node for the open factor and the new closed-residue-field node, so the composite residue-field map is an isomorphism. Step 2 uses the cited open-subscheme factorization node and correctly preserves the unique point `c(z)`. Step 3 applies the new field-through-closed node to the intermediate map. Step 4 cancels the open immersion using the cited reviewed monomorphism leaf, then uses the closed-factorization uniqueness; the final sentence is exactly the algebraically closed-field instance. No step relies on an uncited construction or changes the unit route `sk-thm-p1`.

The item's `proof_deps` is exactly the union of all step `uses`; all cited ids exist and are unmerged. Both new nodes introduce their own objects, cite their source, record multi-kind Mathlib searches with verdicts, and have `created.item` exactly equal to this item. JSON validation, `tools/review_split.py lem-weil-pbc-field-point-factors-through-immersion`, `tools/check_dag.py --cycles`, and `git diff --check` are run before delivery. Review result: pass.
