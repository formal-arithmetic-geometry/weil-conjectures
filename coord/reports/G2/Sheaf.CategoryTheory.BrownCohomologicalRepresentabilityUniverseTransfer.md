## What changed

Added `BrownCohomologicalRepresentabilityUniverseTransferAux.lean`, containing the strictly smaller auxiliary theorem for the universe bookkeeping, and imported it from the target module. The target theorem now has a complete Lean proof that packages the auxiliary representing-by result as `Functor.IsRepresentable`.

## Proved and sorry left

`brownCohomologicalRepresentabilityUniverseTransfer` is proved. The auxiliary theorem `brownCohomologicalRepresentabilityUniverseTransfer_aux` remains a single named `sorry`, with node `lem-pc-brown-representability-universe-transfer-aux`.

## No longer needed

No imports were removed. The original plan’s direct transport steps are encapsulated by the auxiliary theorem; no additional modules were needed.

## Where the brief, the DAG or earlier work was wrong

The DAG marked the entire universe transport as elementary, but Lean requires substantial explicit transport infrastructure. The remaining argument is isolated as a strictly smaller theorem rather than leaving a `sorry` inside the target proof.

## New nodes

Added `lem-pc-brown-representability-universe-transfer-aux` for the universe bookkeeping subargument.

## Second reading by G2

1. **Statements and diff.** Compared both delivered modules with the repository versions. The
target theorem signature is byte-for-byte unchanged; the auxiliary module is new. The target proof
only packages the auxiliary existential into `Functor.IsRepresentable`.
2. **Compilation and axioms.** Compiled both files with `lcompile.py --all`; there are no errors.
The only remaining `sorry` is the named auxiliary theorem below. It is a theorem proof hole, not a
definition hole; the target proof itself is complete.
3. **Split statement.** The remaining hole is
`CategoryTheory.brownCohomologicalRepresentabilityUniverseTransfer_aux`, node
`lem-pc-brown-representability-universe-transfer-aux`. Its docstring gives the complete
universe-transport argument and its source. The statement supplies the representing object needed
by the target, while the target packages it as the `IsRepresentable` class.
4. **Pruning and imports.** Removed the unused proof-only import
`Sheaf.CategoryTheory.BrownCohomologicalRepresentability` from the target module. The remaining
imports are used by declarations or the auxiliary proof interface. The unit route and target
statement are unchanged.
5. **DAG agreement.** The target node records the auxiliary theorem as its proof dependency, and
the auxiliary node records the same theorem and Lean declaration. No target definition or statement
was changed.

## Earlier second reading (a previous round; superseded)

The auxiliary theorem is strictly smaller than the target: it supplies only the universe-transport step, and the target combines it by a complete constructor proof. The target statement and unit route are unchanged.
