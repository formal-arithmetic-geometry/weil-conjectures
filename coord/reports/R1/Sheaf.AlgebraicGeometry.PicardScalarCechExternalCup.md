## What changed

Repaired the returned delivery by moving `picardScalarCech_externalCup` before
`picardScalarCech_externalCup_core`, preserving both signatures. The final theorem
is now the sole unresolved obligation (`:= by sorry`). The core theorem is a
compatibility wrapper whose proof applies the final theorem with the same data and
cover hypotheses. Restored the final node's original comparison/refinement proof
plan and dependencies, and recorded the core node as an application of the final
node.

## Proved and sorry left

No original holes were closed and no new obligations were split off. The remaining
sorry is `AlgebraicGeometry.Scheme.Modules.picardScalarCech_externalCup`. The core
has a complete Lean proof by applying that named theorem.

## No longer needed

None. The final theorem's original proof dependencies remain required by its
unresolved plan; the core wrapper introduces no additional mathematical
obligations or imports.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery made the core theorem the unresolved whole-item helper and
proved the final theorem from it, which the reviewer rejected as a restatement.
The dependency direction is corrected: final is the unresolved theorem and core is
its compatibility wrapper.

## New nodes

None.

## Second reading by R1

1. Compared the delivered module with the repository version. Existing theorem
   signatures are preserved except for the documented repair to
   `picardScalarCech_externalCup_core`, whose cover hypotheses were restored by
   `coord/changes/picard-scalar-cech-external-cup-covers.md`; the final theorem
   signature is unchanged.
2. Compiled the module with `lcompile.py`; it has no errors or warnings. The only
   `sorry` is the named final theorem. The axiom check reports only the permitted
   foundations together with `sorryAx` from that theorem; the core wrapper adds no
   independent axiom.
3. Checked the split-off core statement and its DAG node. It is a true, strictly
   simpler compatibility application of the final theorem, with the restored cover
   hypotheses, and is not a restatement used to prove the final theorem.
4. Read the proof route and imports. The final theorem retains the comparison,
   refinement, and scalar external-cup dependencies; the core uses only the final
   theorem. No unused imports or obsolete proof dependencies were found, and the
   unit route remains recorded.
5. Checked both node JSON files against the declarations and proof directions;
   the final node remains the sole open obligation and the core node records its
   application proof. The cover change record documents the statement repair.

Changed the core theorem order and proof direction, removed the inert `<;> skip`
tactic from the wrapper, and added this second-reading record. No original hole was
closed and no new sorry was added.
