## What changed

Added proof-only imports and a real constructor proof for `isConstructibleSheaf_integral_iff`. The two directional arguments are isolated as named intermediate theorems in `ConstructibleIntegralCoefficientsForward` and `ConstructibleIntegralCoefficientsBackward`.

## Proved and sorry left

`isConstructibleSheaf_integral_iff` is proved by combining the two directional theorems. The intermediate declarations `isConstructibleSheaf_integral_forward` and `isConstructibleSheaf_integral_backward` remain `sorry`, with DAG nodes `q1-constructible-integral-coefficients-forward` and `q1-constructible-integral-coefficients-backward`.

## No longer needed

No imports or existing proof-dependency nodes were removed; both intermediate directions are strictly the two halves of the stated route.

## Where the brief, the DAG or earlier work was wrong

The original proof was wholly `sorry`; no statement or definition was changed.

## Second reading by M2

1. **Statements unchanged.** Compared the delivered item module with the repository version. The existing theorem signature and its docstring are byte-for-byte unchanged; only two proof-only imports and the proof body differ. The two added theorem signatures match their DAG node statements.
2. **Proof checks.** Compiled all three delivered modules with `lcompile.py --all`; they compile without errors or warnings. The main theorem is a genuine constructor proof applying the forward and backward implications. The only remaining `sorry`s are the two named split-off theorems listed above; neither is inside a definition. No forbidden declarations occur.
3. **Split-off statements.** Both directional statements are true strict subgoals of the original equivalence, with the same hypotheses and one implication each. Their docstrings give the source and mathematical argument, and each has a matching DAG node. Searches found no existing declaration with either statement.
4. **Pruning and route.** The proof uses both directional imports and removes no existing import or proof dependency. The unit route is preserved; `sk-thm-p1` remains the unit recorded by the item's node.
5. **DAG agreement.** The item's proof now records the constructor route through the two split nodes, and each split node records its corresponding Lean declaration and proof origin. No definitions or target statements were changed.

Changed only the main proof, added the two proof-only modules and their split nodes, and updated this report.

## New nodes

`q1-constructible-integral-coefficients-forward` records the forward implication and its source, proof route, and Lean declaration.

`q1-constructible-integral-coefficients-backward` records the backward implication and its source, proof route, and Lean declaration.
