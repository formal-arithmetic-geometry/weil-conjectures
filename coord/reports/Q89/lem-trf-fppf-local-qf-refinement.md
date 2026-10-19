Files written:

- `dag/nodes/sec-trace-formula/lem-trf-fppf-local-qf-refinement.json` — item, split; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-fppf-local-qf-neighbourhood.json` — new statement-only Tag 0571 input; no Mathlib match.
- `citations.json` — verbatim quotes for every node used by every proof step.

Attachments: none. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item tag, refinement terminology, and likely declaration names; no sorry-free project declaration states the item exactly. The related finite-free declaration depends on this item and is not an attachment.

WANTED: none.

What was wrong or incomplete in the imported split: the item had no proof and omitted the pointwise Tag 0571 input. I added that genuine smaller statement as an unsplit node. The item statement is unchanged; I added `def-weil-size-convention` to `stmt_deps` because the point-indexed family must be small. Empty base and empty original-index cases are handled explicitly. No source statement error was found.

What remains unfinished: the new Tag 0571 node is intentionally statement-only and remains in the stage-1 queue. No Lean or compiler work was performed.

## Not duplicates

- `lem-trf-fppf-local-qf-neighbourhood` vs `lem-trf-cm-closed-point-flat-quasifinite-slice`: the new node applies to every image point of any flat locally finitely presented morphism; the existing node requires a closed fibre point with a Noetherian Cohen–Macaulay local ring and additionally gives a singleton fibre.

## Review by Q89

I read the imported item and the exact Stacks source at `more-morphisms.tex`, Tag 0572, including its pointwise proof. I also read Tag 0571 in the same file, which is the source of the new neighbourhood node. There is no matching declaration in the read-only slopmaster2 source. I checked the item statement against the Tag 0572 hypotheses and conclusion: the source gives an fppf refinement by maps that are flat, locally of finite presentation, and locally quasi-finite, with an actual factorization through a chosen original covering member.

Step 1 uses the covering definition from `def-pc-fppf-site` for joint surjectivity and the size convention for the point-indexed family. I verified the empty-base case and that an empty original index set forces an empty base. Step 2 applies the new Tag 0571 statement to each chosen covering member and point; its conclusion supplies the factor map, the three morphism properties, and a member whose image contains the chosen point. Thus the resulting family is jointly surjective point-by-point and is a genuine refinement. The three citation quotes were copied verbatim from the cited node statements.

I searched the whole DAG and current blueprint for Tag 0571, `qf-fp-flat-neighbourhood`, and the relevant flat/locally quasi-finite wording before creating the new node. I ran LeanFinder, Loogle, Mathlib grep, and LeanSearch for both the item and the new node using `msearch.py`; the services returned only generic covering, flatness, openness, and quasi-finite declarations, with no theorem constructing either refinement. The new statement was checked on the identity map and on an empty base; the extra Cohen–Macaulay slice node is a special-case result with strictly stronger hypotheses and a different conclusion, so it is not a duplicate. No forbidden literature or SGA source is used.
