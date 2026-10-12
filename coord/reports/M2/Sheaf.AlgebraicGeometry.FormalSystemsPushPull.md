## What changed
Added `FormalSystemsPushPullCore`, a strict intermediate theorem leaving only the affine formal-functions comparison and termwise annihilation as a named hole. The target theorem now combines this core with `coherentFormalModule_annihilated_iff` to obtain kernel and cokernel forks and their uniform annihilation. Added the corresponding DAG node.

## Proved and sorry left
`AlgebraicGeometry.exists_formalSystemsPushPull` is proved. The new declaration `AlgebraicGeometry.exists_formalSystemsPushPull_core` remains `sorry`, with node `lem-weil-pbc-formal-systems-push-pull-core`.

## No longer needed
The target module no longer needs the proof-only imports `AssociatedModulePullback`, `BaseChangeConventions`, `ClosedSubsetProperOverBase`, `CoherentFiniteTypeLocallyNoetherian`, `CoherentFormalModule`, `CoherentKernelCokernelLocallyNoetherian`, `CoherentSupportPowerIdealKills`, `FiniteTypeModuleSupportPullback`, `FormalCompletionFullyFaithfulProper`, `ModulePullbackIdealQuotient`, `Modules.IdealTimesQuasiCoherentAffineSections`, `Modules.QuasiCoherentCokernelImage`, `QuasicoherentFiniteTypeAffine`, `TensorPullback`, `TheoremFormalFunctions`, `AdicCompletionNoetherian`, `PresheafModuleStalkFunctor`, `FiniteFreeComplex`, `EulerChar`, and `Modules.Tilde`; the proof now uses only the core comparison theorem and the existing annihilation equivalence.

## Where the brief, the DAG or earlier work was wrong
The original eleven-step proof plan is too large to realize directly in this stage. The target can be reduced cleanly to the strict intermediate comparison-and-termwise-annihilation statement, after which the existing TFAE theorem supplies the categorical kernel and cokernel conclusion.

## New nodes
`lem-weil-pbc-formal-systems-push-pull-core` records the strict intermediate theorem and its source.

## Earlier second reading (a previous round; superseded)
Second reader: pending assignment. The target proof compiles and preserves the target signature; the added core statement is strictly weaker than the target and is the only remaining sorry.

## Second reading by M2

1. I compared both delivered modules against the repository versions. The target theorem signature is byte-for-byte unchanged; the only interface addition is the separately declared core theorem and its import, recorded by the new DAG node.
2. I compiled the complete sandbox import order successfully. The only remaining `sorry` is the named declaration `AlgebraicGeometry.exists_formalSystemsPushPull_core`; there are no axioms, unsafe declarations, or hollow definitions. The target proof uses the core theorem and the existing TFAE characterization without changing any statement.
3. The split-off core statement is true as a strict weakening of the target: it asks only for coherence, a comparison morphism, and termwise kernel/cokernel annihilation, omitting the categorical kernel and cokernel witnesses. Its proof source and node are recorded, and no duplicate declaration was found in the library.
4. The target proof follows the shortest available route from the core result through `coherentFormalModule_annihilated_iff` and `List.TFAE.out`; no imports could be removed because the existing interface and proof dependencies still require them. The unit route remains represented by the target node and the new core node.
5. The DAG node for `lem-weil-pbc-formal-systems-push-pull-core` matches the Lean declaration, including its statement, proof dependency, source, and `split` status. No existing node or target statement was altered.

Changed during second reading: no Lean proof or statement changes were necessary; this report section records the checks above.
