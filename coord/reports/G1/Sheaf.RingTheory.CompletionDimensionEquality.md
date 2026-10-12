## What changed

Proved `RingTheory.completion_dimension_eq` using the flat height formula for the completion map. The completion is Noetherian and local, its maximal ideal is the mapped maximal ideal, and the quotient fibre ideal maps to bottom.

## Proved and sorry left

Closed the only sorry, `RingTheory.completion_dimension_eq`. No sorries remain.

## No longer needed

No additional DAG nodes or modules were needed beyond the existing Mathlib height formula and completion properties.

## Where the brief, the DAG or earlier work was wrong

The proof plan's three project dependency nodes are already realized by Mathlib declarations; no correction was needed.

## Second reading by G1

1. **Statements and interfaces.** Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only proof imports and the proof body differ. Verdict: pass.
2. **Proof validity and axioms.** Compiled the module with `lcompile.py`; it compiles successfully (only style linter warnings for proposition-valued `letI`s). The proof contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. It uses the Mathlib flat-height theorem together with the proved completion-Noetherianity declaration. Verdict: pass.
3. **Split statements and search.** No statements were split off and no new nodes were added. The existing theorem is proved directly; the old flat-height, local-completion, and faithfully-flat project nodes are not needed as Lean dependencies because their required facts are supplied by Mathlib declarations. Verdict: pass.
4. **Pruning and imports.** Each added proof-only import is required: removing `AdicCompletion.LocalRing`, `AdicCompletion.AsTensorProduct`, or `Ideal.KrullsHeightTheorem` makes compilation fail. The public imports remain those needed by the theorem interface. The DAG proof dependencies were pruned to `lem-weil-pbc-adic-completion-noetherian`, which is the project declaration actually used. Verdict: pass.
5. **DAG and unit route.** The theorem node's proof, proof origin, and proof dependencies now agree with the Lean proof. The theorem remains under unit `sk-thm-p1`; no unit statement or realized route was changed. Verdict: pass.

Changed the proof-dependency metadata and added this second-reading record. No holes were added; the only hole, `RingTheory.completion_dimension_eq`, was closed.
