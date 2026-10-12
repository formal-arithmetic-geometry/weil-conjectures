## What changed

Proved `CategoryTheory.initial_iff_essentiallyConstantProDiagram` in
`Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantCofinal`, with its entire
signature and public imports unchanged. Two proved private helpers construct the
restricted and extended witnesses. The proof works directly with the common-stage
condition, Mathlib's cofiltered initiality criterion, and cone extension.
Updated the theorem's proof docstring and its node's proof, proof_deps and
proof_origin to match this shorter route. No definition or interface changed.

## Proved and sorry left

Closed the single hole in `CategoryTheory.initial_iff_essentiallyConstantProDiagram`
(node `lem-pur-essential-constant-cofinal-0a1s`). No sorry remains in the item;
no hole was added or split off. Both private helpers are proved. Single-file
compilation passes without warnings. The delivery dry run checks every declaration's
axioms. This is a complete proof, not a decomposition through unproved statements.

## No longer needed

Removed proof imports:
- `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantProCriterion`
- `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantProHomColimit`

The corresponding nodes `lem-pur-essential-constant-pro-criterion-05py` and
`lem-pc-essentially-constant-pro-hom-colimit` are no longer dependencies of this
item. Their subproofs and Hom-colimit comparison machinery are unnecessary here;
other callers may still need them. Retained `lem-weil-pbc-initial-functor-limit`
for its Mathlib cone-extension clause, and the definition node. No unit-level
statement or step is bypassed: `sk-def-sf-operations` has empty realized statement
and step lists.

## Where the brief, the DAG or earlier work was wrong

The Hom-colimit route was valid but unnecessarily long. Directly lifting the
factorization witnesses proves both directions and both prescribed-cone clauses.
No mathematical error or tool workaround was required. The node's pre-existing
source field mentions 0A1S; its proof_origin and the Lean docstring already correctly
identify the pro form as 0A1T, and that source field was left unchanged under the
stage-3 field-ownership rules. Searches found the Mathlib initiality and cone
extension APIs, not an existing essential-constancy theorem.

## Second reading by Y3

1. I compared the delivered Lean module with the repository version. The existing theorem
   signature, all declaration signatures, and the target statement are byte-for-byte unchanged;
   only proof imports, proof text, and the node's proof metadata differ.
2. I compiled the module with `lcompile.py`; it compiles without errors or warnings. There are no
   `sorry`s, axioms, unsafe declarations, or hollow definitions. The two private witness helpers
   are fully proved, and the proof uses only the permitted initiality and cofiltered-category APIs.
3. The only changed node is `lem-pur-essential-constant-cofinal-0a1s`. Its statement is unchanged,
   and its proof, `proof_deps`, and `proof_origin` now match the direct Lean proof. No new
   statements were split off; the existing Mathlib/library declarations were searched before
   retaining the direct construction.
4. Reading from the target downward, the direct restriction and cone-extension constructions are
   shorter than the former Hom-colimit route. The removed proof-only imports and their dependency
   nodes are genuinely unused by the compiled proof; the definition and initial-functor dependency
   remain. No unit-level statement or step is bypassed.
5. The unit route is preserved: the item's unit is `sk-def-sf-operations`, whose realized
   statement and step lists are empty. The report's proof and pruning claims therefore agree with
   the DAG and the compiled module.

I changed only this report section after the initial review, to record the required second-reader
checks; no Lean code or statement required repair.
