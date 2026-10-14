## What changed

Repaired `cartier_equality` by making its finite-generation hypothesis explicit as
`IntermediateField.FG (⊤ : IntermediateField k K)`, as required by upstream review #1428.
The existing complete proof and proof imports were retained. The copied DAG node's
Lean statement was updated to match the repaired interface.
Change record: `coord/changes/cartier_equality.md`.

## Proved and sorry left

`cartier_equality` remains fully proved; no `sorry` declarations were added or left.

## No longer needed

None. The existing complete-intersection and cotangent-model imports remain required by
the proof.

## Where the brief, the DAG or earlier work was wrong

The earlier repair attempt treated the already-proved module as unchanged and did not
materialize the required statement repair. The upstream review specifically requires
an explicit finitely generated field-extension hypothesis. The repaired statement is
definitionally equivalent to the notation previously used, while recording the intended
interface directly.

## New nodes

None. The existing node was copied and its Lean signature metadata was synchronized with
the repaired statement.

## Earlier second reading (a previous round; superseded)

Independent reading remains to be performed by the V2 second reader. The repaired
signature is definitionally equivalent to the existing call sites and the proof compiles.

## Second reading by V2

1. **Interface and accidental changes.** Compared the delivered module with the repository
   version. The theorem statement is unchanged from the repository's repaired interface;
   the DAG Lean statement matches it byte for byte. Verdict: pass.
2. **Proof validity.** Compiled the module and all sandbox modules with `lcompile.py`; no
   errors, warnings, `sorry`, or forbidden declarations occur. The proof uses only the
   declared finite-generation hypothesis and the cited complete-intersection lemmas.
   Verdict: pass.
3. **Statements and nodes.** No statements were split off and no new nodes were added.
   The existing node's statement, proof dependencies, and proof origin agree with the
   implementation, and the qualified `IntermediateField.FG` hypothesis is true and exactly
   expresses finite generation of the top intermediate field. Verdict: pass.
4. **Pruning and imports.** The public imports are needed for the theorem's types; the
   proof-only imports supply the finite transcendence basis, complete-intersection model,
   and cotangent comparison used by the proof. No removable import or proof dependency was
   found. Verdict: pass.
5. **Unit route and edge cases.** The proof retains the unit's complete-intersection and
   cotangent-model route, and the finite-extension conclusion follows by zero transcendence
   degree and cancellation of natural-number casts. Verdict: pass.

Changed nothing during this second reading: the sandbox already contained the repaired
qualified hypothesis, synchronized DAG metadata, and a compiling complete proof.
