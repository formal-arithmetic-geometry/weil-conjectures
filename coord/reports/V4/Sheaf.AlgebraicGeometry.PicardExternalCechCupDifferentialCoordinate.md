## What changed
Added the canonical-degree intermediate theorem `picardExternalCechCupDegreeMaps_comm_ι_rfl` and used it to transport the inclusion identity across `hpq : p + q = n` in `picardExternalCechCupDegreeMaps_comm_ι`. The intermediate theorem isolates the signed Alexander–Whitney coordinate calculation.

## Proved and sorry left
The target theorem `picardExternalCechCupDegreeMaps_comm_ι` is proved by substitution and application of the canonical-degree theorem. The canonical-degree theorem `picardExternalCechCupDegreeMaps_comm_ι_rfl` remains `sorry`; it is a strictly canonical-degree coordinate calculation and has a new DAG node with the same name.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The original node's proof plan requires a substantial signed face calculation. This delivery isolates that calculation as a canonical-degree intermediate theorem so the equality transport is checked by Lean.

## New nodes
`lem-sc-picard-external-cech-cup-differential-coordinate-rfl` records the canonical-degree intermediate theorem.

## Second reading by V4

1. **Visible changes and signatures.** Compared the delivered module with the repository version. Existing declarations and definitions retain byte-identical signatures; the only existing proof change is the transport proof of `picardExternalCechCupDegreeMaps_comm_ι`. Verdict: pass.
2. **Compilation and axioms.** Compiled the module with `lcompile.py`; it compiles cleanly after the comment whitespace fix. The only remaining `sorry` is the named theorem `picardExternalCechCupDegreeMaps_comm_ι_rfl`, and no forbidden declaration forms were introduced. Verdict: pass, with that explicit split remaining.
3. **New statement.** Checked the canonical-degree theorem against the signed Alexander--Whitney calculation and its bidegree hypotheses. It is a strict reduction of the original target and has a matching node, source, proof plan, and declaration metadata. Verdict: pass.
4. **Route and pruning.** The target proof now follows the shortest available route: substitution of `hpq` followed by the canonical-degree theorem. No imports or prior proof dependencies are unused, and the unit route is preserved. Verdict: pass.
5. **DAG agreement.** Updated the target node's `proof`, `proof_deps`, and `proof_origin` to record the actual reduction, and retained the new split node with its dependency metadata. Verdict: pass.

Changed the comment whitespace, recorded the target-node proof reduction, and added this second-reading record. The target hole is closed by decomposition; the canonical-degree hole remains split under `lem-sc-picard-external-cech-cup-differential-coordinate-rfl`.
