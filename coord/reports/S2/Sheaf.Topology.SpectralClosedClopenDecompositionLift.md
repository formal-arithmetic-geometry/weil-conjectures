## What changed

Proved `TopCat.spectral_closed_clopen_decomposition_lift` in the item module. The proof
constructs the two specialization hulls of the closed pieces, proves they partition the
space using connectedness, proves closedness using the proconstructible specialization
lemma, and identifies their intersections with `Z`. The existing imports are all used.

## Proved and sorry left

The item's theorem `TopCat.spectral_closed_clopen_decomposition_lift` is proved. No
`sorry` remains in the delivered module.

## No longer needed

None. The imports `Sheaf.Topology.ProconstructibleClosureSpecialization` and
`Sheaf.Topology.SpectralGeneralizations` and the three public Mathlib imports are used.

## Where the brief, the DAG or earlier work was wrong

No error found. The proof follows the five steps recorded in the node.

## Second reading by S2

1. **Statements and accidental changes.** Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only the theorem proof was filled in. No change record is needed.

2. **Proof and axioms.** Compiled `lean/Sheaf/Topology/SpectralClosedClopenDecompositionLift.lean` successfully with `lcompile.py`. The module has no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`; the theorem's only additional `sorryAx` dependency in a scratch `#print axioms` check comes from imported open nodes, while the theorem proof itself is complete.

3. **Split-off statements.** No statements were split off by this delivery. The proof uses the existing imported topology lemmas and introduces only local `have` declarations. No duplicate library or Mathlib statement was added.

4. **Route and pruning.** The proof follows the five-step route in the DAG: closed compact pieces, specialization hulls, connected partition, closedness by proconstructible specialization, and restriction equalities. The unit route is preserved. All listed imports are used, so no proof dependency or import was pruned.

5. **DAG agreement.** The node's statement, proof dependencies, and proof origin agree with the Lean proof and remain unchanged. The unit's `realized` route is unaffected.

No changes were necessary beyond this second-reading report.
