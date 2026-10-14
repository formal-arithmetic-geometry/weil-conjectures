## What changed

Retained the repaired `IntermediateField.FG (⊤ : IntermediateField k K)` hypothesis and
complete proof of `cartier_equality`.  Clarified the proof-local derivation of zero
transcendence degree in the finite-dimensional case with an explicit `by exact` block.
The public signature and imports are unchanged.

## Proved and sorry left

`cartier_equality` is proved.  No `sorry`s remain and no new holes were introduced.
This is the queued repair for upstream review #1428; the current baseline already contains
the corrected statement and proof, so this repair closes no additional baseline hole.

## No longer needed

None.  The complete-intersection model and fraction-field cotangent model imports are
used; no DAG dependency or import was pruned.

## Where the brief, the DAG or earlier work was wrong

The old `Algebra.FiniteType k K` hypothesis was too strong for the intended finitely
generated field extension statement, as identified by upstream review #1428.  The current
module correctly uses `IntermediateField.FG (⊤ : IntermediateField k K)`.  The proof follows
the existing Cartier-equality DAG node and its complete-intersection and cotangent-model
dependencies.

## Second reading by H1

1. Compared the delivered module with the repository version. The public theorem statement,
   hypotheses, conclusion, definitions, visibility, and imports are byte-for-byte unchanged;
   the only proof edit is an explicit `by exact` wrapper around `trdeg_eq_zero`. Verdict: pass.
2. Compiled the module with `lcompile.py`; it compiles cleanly with no errors or warnings.
   The file contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`, and
   no definition contains a hole. Axiom auditing of the theorem reports only the permitted
   foundational axioms. Verdict: pass.
3. No statements were split off and no new nodes were added. The theorem retains the exact
   `IntermediateField.FG (⊤ : IntermediateField k K)` hypothesis and all four conclusions;
   finite and zero-transcendence-degree edge cases are covered by the final implication.
   No duplicate statement search is needed. Verdict: pass.
4. Read the proof top down and checked its imports and DAG dependencies. The proof uses the
   finite transcendence basis, complete-intersection model, cotangent model, rank-nullity,
   quotient dimension, and `trdeg_eq_zero` routes recorded by the node. All imports are used,
   no dependency or import can be pruned, and the unit route remains unchanged. Verdict: pass.
5. Compared the node metadata with the retained Lean declaration. The recorded statement,
   proof steps, proof dependencies, source, and unit agree with the implementation; there are
   no new nodes or change records requiring review. Verdict: pass.

Second reading changed only this report section. No holes were closed or added, no statements
or definitions changed, and no imports or nodes were pruned.
