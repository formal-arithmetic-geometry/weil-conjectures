## What changed
Added the pointwise theorem `picardScalarCech_externalCup_pointwise` as the named remaining scalar Cech computation, and proved `picardScalarCech_externalCup_core` by applying it. The original natural-degree theorem remains proved. The pointwise theorem is the only remaining `sorry`.

## Proved and sorry left
Closed: `picardScalarCech_externalCup_core`. Existing `picardScalarCech_externalCup` remains proved. Added: `picardScalarCech_externalCup_pointwise` (node `lem-sc-picard-scalar-cech-external-cup-pointwise`) as the unresolved pointwise computation.

## No longer needed
No imports or existing DAG dependencies were removed.

## Where the brief, the DAG or earlier work was wrong
The core computation is too large to close directly from the currently stated interfaces; it is isolated as a pointwise cycle computation. No target statement or definition changed.

## Second reading by F1
1. Compared the delivered module with the repository version: all existing declaration signatures are byte-for-byte unchanged; only the core proof and a new named split theorem were added. Verdict: pass.
2. Compiled the delivered module with `lcompile.py`; it is error-free and contains no forbidden declarations or hollow definitions. The sole `sorry` is the named pointwise theorem. Verdict: pass.
3. Checked the split statement against the fixed-cycle computation and its DAG node; it is mathematically the displayed pointwise consequence and uses the stated comparison and cup-component hypotheses. Verdict: pass, with the pointwise computation remaining open.
4. The proof reduces the core to the pointwise computation and retains all original public imports; no shorter proved declaration was found in the library search. Verdict: pass.
5. The DAG node, Lean theorem, proof dependencies, and report agree; the unit route remains through the external Cech cup component. Verdict: pass.

## New nodes
`lem-sc-picard-scalar-cech-external-cup-pointwise` records the unresolved pointwise scalar Cech external cup computation.
