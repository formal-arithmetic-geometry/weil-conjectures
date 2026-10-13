## What changed

Repaired the Cartier equality interface requested by upstream review #1428 by
stating finite generation with the canonical qualified notation
`(⊤ : IntermediateField k K).FG`. The proof remains the complete
finite-transcendence-basis and complete-intersection rank-nullity argument, and
compiles against the repaired interface.

## Proved and sorry left

`cartier_equality` is proved (1 of 1 declarations), with only `propext`,
`Classical.choice`, and `Quot.sound` in its transitive axiom check. The repository
version already contains this proof: holes closed by this delivery: none; holes
added: none; net hole reduction: 0. No `sorry` remains in the delivered module,
and no statements were split off.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The inherited repair already uses the correct hypothesis
`IntermediateField.FG (⊤ : IntermediateField k K)`. The requested dot notation
is definitionally identical, not a further mathematical repair. This delivery
records that notation explicitly in Lean and in the node Lean signature. The
existing natural-language statement and statement-change history are preserved.
The caller using `IntermediateField.fg_top` remains definitionally compatible. The change record is `coord/changes/cartier-equality-qualified-fg.md`.

## New nodes

None.

## Earlier second reading (a previous round; superseded)

The module compiles cleanly with the qualified FG hypothesis. The direct caller
`PthRootResidueDimensionBalance` continues to compile, and the copied DAG node
records the same interface and repair rationale.

## Second reading by Y3

1. Compared the delivered module with the repository using `diff`: the sole
   signature edit is the reported FG notation; the complete conclusion and proof
   body are byte-for-byte unchanged. A scratch `rfl` proof checks that the old
   and new hypotheses are definitionally equal. No definitions or targets change.
   Verdict: pass, with the change recorded explicitly.
2. Compiled the module cleanly through `lcompile.py`. Scanned the delivery for
   `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, and `extern`: none.
   A scratch copy with `#print axioms cartier_equality` reports exactly `propext`,
   `Classical.choice`, and `Quot.sound`, without `sorryAx`. Compiled the unchanged
   direct caller `PthRootResidueDimensionBalance` against a scratch overlay of the
   delivered module. Verdict: pass.
3. There are no new or split-off statements, nodes, or data definitions. The proof
   eliminates existence witnesses locally; it does not define an arbitrary object
   from an unproved existence result. Checked the zero-transcendence-degree and
   empty-generating-set cases: the indexing by `Fin 0` and the natural-number
   dimension calculation need no positivity assumption. Verdict: pass.
4. Read the finite-generation-to-basis conversion, both model statements, and the
   kernel/cokernel dimension argument. Rank-nullity gives rank + kernel = c;
   the quotient formula gives cokernel + rank = n; c ≤ n and n-c=d yield
   d + kernel = cokernel without truncated subtraction. Cardinal casting and
   the finite-extension clause preserve this equality. Searched the library and
   pinned Mathlib for `cartier_equality` and combinations of `trdeg`, `finrank`,
   `H1Cotangent`, and `Kaehler`: no shorter general theorem was found (the
   separably-generated differential theorem has additional hypotheses).
   Signature imports expose the relevant definitions; basis, linear-algebra and
   model imports used only by the proof are plain imports. Every old proof
   dependency is still used, either through the two model lemmas or its recorded
   Mathlib match, so none is pruned. Read `sk-thm-p1.json`: neither its realized
   statement nor any realized step is bypassed or changed. Verdict: pass.
5. Compared the node JSON semantically with the repository. Only its Lean
   signature needs the notation update; its existing proof, dependencies and
   document origin describe the proof as written. There are no new nodes to audit.
   Restored the original statement-change history, which the first worker had
   overwritten despite leaving the natural-language statement unchanged.
   Verdict: pass after that metadata repair.

Second reading changed the report to state zero newly closed holes, repaired the
change record's declaration heading, full old/new signatures and downstream-user
table, and preserved the node's existing statement-change history. No proof
body or import was changed. The 232 downstream users retain their statements'
meaning by definitional equality; only the one direct caller mentions this theorem
and it compiles without adaptation.
