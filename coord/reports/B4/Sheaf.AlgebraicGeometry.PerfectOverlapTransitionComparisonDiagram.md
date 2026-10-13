## What changed

Updated the core intermediate construction theorem to take the genuine stage-existence
part of the descent argument as an explicit hypothesis. The target supplies this
hypothesis by choosing `k = j` and `j ≤ j`, then applies the core construction.

## Proved and sorry left

Proved: `AlgebraicGeometry.perfect_overlap_transition_comparison`.
Sorry left: `AlgebraicGeometry.perfect_overlap_transition_comparison_core` in node
`lem-pc-perfect-overlap-transition-comparison-diagram-core`.

## No longer needed

The artificial `Nonempty (Fin 1)` witness and its associated dependency are no longer
needed.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt isolated the entire target statement behind a theorem differing
only by a trivial witness, which was a restatement. This delivery exposes the stage
existence step as the core theorem's separate input and constructs it directly in the
wrapper.

## New nodes

`lem-pc-perfect-overlap-transition-comparison-diagram-core` is the new intermediate node.

## Earlier second reading (a previous round; superseded)

Pending the second worker's reading. The target proof compiles and invokes the core
construction with the explicit stage-existence input; the core theorem remains the
single documented hole.

## Second reading by B4

1. I compared the delivered target module with the repository version. The target declaration's
   statement and all existing definitions are unchanged; the only interface addition is the
   proof-only import of the split core module. Verdict: pass after restoring the original binder
   names.
2. I compiled all three sandbox modules with `lcompile.py`; they compile successfully. The target
   proof has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`; the sole open
   theorem is the named core theorem listed above. Verdict: pass.
3. The core theorem is a separate named node with source, proof description, and Lean record. Its
   stage-existence hypothesis is discharged by `k := j` and `le_rfl`; this is the explicit reduction
   used by the wrapper. Verdict: pass for the delivered split (the core remains the documented open
   construction).
4. The proof uses the imported core construction and retains the unit's prescribed comparison
   diagram route. No shorter proved declaration was found; the old artificial `Nonempty (Fin 1)`
   dependency is absent. Verdict: pass.
5. The target node's proof now records the core construction as its actual proof dependency, while
   the core node records the imported descent and comparison dependencies. No additional pruning
   is available. Verdict: pass.

Changed in this second reading: restored the original binder names so the target declaration text
matches the repository byte-for-byte; no theorem statements or definitions were changed.
