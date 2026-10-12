## What changed
Added the objectwise exactness glue theorem and reduced the nerve exactness theorem to it. The glue theorem remains a named sorry for the categorical reflection argument.

## Proved and sorry left
The target theorem `presheafFreeNerveComplex_exactAt` is reduced to the objectwise theorem. Sorry remains in `exactAt_of_presheaf_evaluations` (node `lem-sc-presheaf-free-nerve-exact-eval-glue`) and `presheafFreeNerveComplex_exactAt_eval` (node `lem-sc-presheaf-free-nerve-exact-eval`).

## No longer needed
The attempted explicit inverse construction and `Mathlib.CategoryTheory.Functor.ReflectsIso.Exact` import are not needed.

## Where the brief, the DAG or earlier work was wrong
The original DAG omitted the categorical objectwise-to-presheaf exactness glue as a separately stated result.

## New nodes
`lem-sc-presheaf-free-nerve-exact-eval-glue` records the objectwise reflection statement.

## Earlier second reading (a previous round; superseded)
The target proof is complete and uses only the two strictly lower intermediate statements; both remaining sorries are separately named and recorded as nodes.

## Second reading by N1

1. Compared the delivered module with the repository version. The existing definition and target theorem signatures are unchanged byte for byte; only the target proof and two named intermediate declarations were added.
2. Compiled `lean/Sheaf/CategoryTheory/Sites/PresheafFreeNerveExact.lean` with `lcompile.py`; it succeeds. The only remaining `sorry`s are the two named split theorems listed above, and no forbidden declarations or hollow definitions were introduced.
3. Checked the two split statements against their intended categorical and objectwise claims. Both are true and strictly simpler than the target; neither merely restates the target. The evaluation theorem is the positive-degree objectwise reduction, while the glue theorem is the independent reflection step.
4. The target proof follows the stated shortest route through evaluation and glue. Existing imports remain needed for the definitions and evaluated nerve theorem; no additional proof-only imports were introduced. The unit route still realizes the exactness target through the evaluation step and categorical glue.
5. Checked the DAG records and proof dependencies against the Lean declarations. The target uses the glue theorem, and the evaluation theorem records the set-Cech resolution dependency. No old proof dependency is used by the new target proof except those retained by the intermediate theorem.

Changed in this second reading: corrected the evaluation node's statement dependencies to remove a spurious self/target dependency; no Lean signatures or proofs required repair.
