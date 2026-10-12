## What changed
Added `ConeHorizontalQuotientIsoExists`, splitting the objectwise existence construction into a named intermediate theorem with its proof deferred, and proved uniqueness in `ConeHorizontalQuotientIso` by epi cancellation of the quotient projection. Added the corresponding DAG node.

## Proved and sorry left
The original theorem `HomologicalComplex₂.coneHorizontal_quotient_iso` is proved. The intermediate theorem `HomologicalComplex₂.coneHorizontal_quotient_iso_exists` remains `sorry` and is recorded by node `lem-sp-cone-horizontal-quotient-iso-exists`.

## No longer needed
No stated proof dependency was removed; all three dependencies remain required by the existence statement.

## Where the brief, the DAG or earlier work was wrong
The full objectwise construction is too large to complete in this item; it was split at the strictly smaller existence component, while uniqueness is proved directly from epimorphicity.


## New nodes
`lem-sp-cone-horizontal-quotient-iso-exists` records the deferred objectwise existence construction.

## Second reading by P3

1. **Visible declarations:** Compared the delivered module with the repository version. The existing theorem signature is unchanged byte for byte; the only interface addition is the explicitly recorded existence theorem in its new module and node.
2. **Proof and axioms:** Compiled both sandbox modules successfully with `lcompile.py`. The target proof uses the existence theorem and epi cancellation; no forbidden declarations or hollow definitions were added. The target's remaining `sorryAx` is inherited solely from the named split-off existence theorem.
3. **Split-off statement:** Checked `coneHorizontal_quotient_iso_exists` against the target: it is the same construction with uniqueness removed, hence strictly simpler and sufficient for the uniqueness proof. Its docstring records the objectwise cokernel argument, and its DAG node matches the Lean declaration.
4. **Pruning and route:** The proof retains the unit route through `ConeHorizontalProjection`, `ConeHorizontalStepStable`, and `FilteredComplexSubquotients`; the added import is proof-only (`import`), and no prior dependency was unused.
5. **DAG consistency:** Verified the existing target node's route is extended by the existence node and that the new node records its statement, source, proof dependencies, origin, module, and declaration consistently.

Changed during second reading: removed an accidental scratch `#print axioms` line after verification; no substantive proof or statement changes were needed.
