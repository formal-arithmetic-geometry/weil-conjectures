## What changed

Repaired the queued upstream-review #1428 item by making the finitely generated
field-extension hypothesis explicit as `IntermediateField.FG (⊤ : IntermediateField k K)`.
The theorem proof was already complete in the supplied branch and compiles
unchanged; the old `[Algebra.FiniteType k K]` formulation is absent from the
delivered interface. Updated the DAG statement/interface record and added the
change record.

## Proved and sorry left

`cartier_equality` has no `sorry` and remains fully proved. No new holes were
added.

## No longer needed

None. The complete-intersection and cotangent-model imports remain required by
the proof.

## Where the brief, the DAG or earlier work was wrong

The earlier worker correctly observed that the source branch already contained
the repaired finitely generated-field statement and proof, but its unchanged
copy was rejected by `deliver3.py` as stale. This delivery records the queued
repair as an explicit qualified `IntermediateField.FG` hypothesis while
preserving the corrected mathematical statement.

## Earlier second reading (a previous round; superseded)

Pending the independent second reader.

The change record is `coord/changes/cartier-equality-fg-hypothesis.md`.

## Second reading by Q4

1. **Interface and accidental changes.** Compared the delivered module with
`lean/Sheaf/Paper/CartierEquality.lean` in the repository. The theorem body and
all declarations are unchanged; the only declared interface edit is the
qualified spelling `IntermediateField.FG (⊤ : IntermediateField k K)`, recorded
in `coord/changes/cartier-equality-fg-hypothesis.md`. No target statement or
definition was altered.

2. **Proof and axioms.** Compiled the module with `lcompile.py`; it compiles
without errors or warnings and contains no `sorry`, `axiom`, `unsafe`,
`opaque`, `extern`, or `implemented_by`. A scratch `#print axioms
cartier_equality` reports only `propext`, `Classical.choice`, and `Quot.sound`.

3. **Statements and split nodes.** `cartier_equality` is the sole declaration
and is fully proved; no split-off theorem or new hole was added. The theorem's
qualified FG hypothesis is definitionally the same as the prior spelling and
is exactly the finite-generation assumption in the node. The existing node's
proof and dependencies agree with the imports and proof route; no new node is
needed and no Mathlib/upstream duplicate was introduced.

4. **Pruning and imports.** Checked every import against names used by the
proof. The complete-intersection model and cotangent-model imports are both
used, as are the listed Mathlib imports; no import can be removed. The DAG
proof dependencies therefore remain unchanged, and no old dependency is
prunable.

5. **Unit route.** The proof retains the complete-intersection and cotangent
model route recorded by `lem-weil-pbc-cartier-equality` and its `sk-thm-p1`
unit context; no unit statement or realized step is bypassed.

The only change made during this second reading was appending this review;
the module and DAG already passed compilation and consistency checks.
