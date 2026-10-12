## What changed

Proved `RingHom.exists_lift_of_field_charP` using Mathlib formal smooth lifting. Handles the subsingleton target separately; in the nontrivial case constructs the characteristic-p algebra and formal smoothness from the cotangent vanishing statement and vector-space freeness.

## Proved and sorry left

Closed `RingHom.exists_lift_of_field_charP`; no sorry remains.

## No longer needed

The explicit induction through powers of `J` is unnecessary because `Algebra.FormallySmooth.exists_lift` already performs nilpotent induction. The listed square-zero lifting and vector-space-projective nodes are used through Mathlib's formal smoothness construction; no additional imports were needed beyond the existing cotangent module and Mathlib smoothness/characteristic modules.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan is longer than needed: Mathlib's `exists_lift` directly handles arbitrary nilpotent ideals once formal smoothness is assembled.

## Second reading by H2

1. **Statements unchanged.** Compared the delivered Lean module with the repository version. The theorem signature and all existing declarations are unchanged; only proof imports and the theorem proof differ.
2. **Proof validity.** Compiled the module with `lcompile.py`; it succeeds with no errors and no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The proof handles the subsingleton case directly, and in the nontrivial case constructs formal smoothness from the characteristic-p H1-cotangent vanishing and the standard free/projective differential module, then applies Mathlib's nilpotent lifting theorem. The node proof and dependencies were updated to match this route.
3. **Split-off statements.** No new split-off theorem was added. The existing target statement is true and unchanged; the proof uses the existing H1-cotangent node and Mathlib declarations only.
4. **Pruning.** The former square-zero lifting and vector-space-projective DAG dependencies are no longer used directly and were removed from `proof_deps`; the explicit induction is subsumed by `Algebra.FormallySmooth.exists_lift`. The added imports are proof-only imports.
5. **Unit route.** The unit's target node remains realized by this module. The route is shortened below the unit level through Mathlib's formally smooth nilpotent lifting API, while retaining the required characteristic-p H1-cotangent ingredient.

Changed the proof to avoid linter `letI` warnings and updated the node's `proof`, `proof_deps`, and `proof_origin` to reflect the actual proof. No holes were added; `RingHom.exists_lift_of_field_charP` is closed.
