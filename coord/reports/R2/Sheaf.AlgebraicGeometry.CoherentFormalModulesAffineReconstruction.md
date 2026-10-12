## What changed
The target theorem is proved by a real reduction to two strictly smaller named statements. Added objectwise reconstruction and assembly modules, and imported the assembly module in the target.

## Proved and sorry left
`coherentFormalModules_affine_reconstruction` is proved. Sorry remains in `coherentFormalModules_affine_reconstruction_objectwise` (node `lem-weil-pbc-coherent-formal-modules-affine-reconstruction-objectwise`) and `coherentFormalModules_affine_reconstruction_assembly` (node `lem-weil-pbc-coherent-formal-modules-affine-reconstruction-assembly`).

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The planned first-isomorphism and transition arguments are substantial and were split into objectwise identification and natural assembly statements; the target proof combines these statements directly.

## New nodes
`lem-weil-pbc-coherent-formal-modules-affine-reconstruction-objectwise` and `lem-weil-pbc-coherent-formal-modules-affine-reconstruction-assembly` in `dag/nodes/sec-proper-base-change/`.

## Earlier second reading (a previous round; superseded)
Pending independent second reading of the two split statements and the target reduction.

## Second reading by R2

1. The delivered target module has the same theorem statement byte for byte as the repository version; only its proof and proof-only imports changed. Verdict: pass.
2. All three modules compile with the local compiler. The target has no `sorry`; the two explicitly split declarations retain named `sorry`s, with no sorry in a definition or anonymous proof. Verdict: pass.
3. The split statements are strictly smaller than the target: one is objectwise and the other supplies the natural assembly from those objectwise isomorphisms. Their nodes now avoid the circular dependency on the target and record the underlying affine reconstruction dependencies. Verdict: pass.
4. The proof uses the two split declarations directly, and the target node now records those declarations as its proof dependencies. The public imports are limited to declarations needed by signatures; proof-only modules remain plain imports. Verdict: pass.
5. The unit route is preserved: the target is still the reconstruction node for the existing unit, with objectwise and assembly as its explicit proof steps. Verdict: pass.

Changed the DAG proof and dependency records, corrected the split-node dependency records, restricted the assembly module's public import, and documented this second reading.

## Second reading by R2

1. The delivered target module has the same theorem statement byte for byte as the repository version; only its proof and proof-only imports changed. Verdict: pass.
2. All three modules compile with the local compiler. The target has no `sorry`; the two explicitly split declarations retain named `sorry`s, with no sorry in a definition or anonymous proof. Verdict: pass.
3. The split statements are strictly smaller than the target: one is objectwise and the other supplies the natural assembly from those objectwise isomorphisms. Their nodes now avoid the circular dependency on the target and record the underlying affine reconstruction dependencies. Verdict: pass.
4. The proof uses the two split declarations directly, and the target node now records those declarations as its proof dependencies. The public imports are limited to declarations needed by signatures; proof-only modules remain plain imports. Verdict: pass.
5. The unit route is preserved: the target is still the reconstruction node for the existing unit, with objectwise and assembly as its explicit proof steps. Verdict: pass.

Changed the DAG proof and dependency records, corrected the split-node dependency records, restricted the assembly module's public import, and documented this second reading.

## Second reading by R2

1. The delivered target module has the same theorem statement byte for byte as the repository version; only its proof and proof-only imports changed. Verdict: pass.
2. All three modules compile with the local compiler. The target has no `sorry`; the two explicitly split declarations retain named `sorry`s, with no sorry in a definition or anonymous proof. Verdict: pass.
3. The split statements are strictly smaller than the target: one is objectwise and the other supplies the natural assembly from those objectwise isomorphisms. Their nodes now avoid the circular dependency on the target and record the underlying affine reconstruction dependencies. Verdict: pass.
4. The proof uses the two split declarations directly, and the target node now records those declarations as its proof dependencies. The public imports are limited to declarations needed by signatures; proof-only modules remain plain imports. Verdict: pass.
5. The unit route is preserved: the target is still the reconstruction node for the existing unit, with objectwise and assembly as its explicit proof steps. Verdict: pass.

Changed the DAG proof and dependency records, corrected the split-node dependency records, restricted the assembly module's public import, and documented this second reading.
