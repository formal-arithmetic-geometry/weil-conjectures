## What changed
Added a scalar-composite intermediate theorem and used the existing algebraic annihilation criterion to reduce the target to that theorem.

## Proved and sorry left
The target theorem is proved from `coherentFormalModule_affine_limit_scalar_composites` and `LinearMap.annihilated_of_scalar_composites`. The new scalar-composite theorem remains `sorry`.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The full geometric construction of compatible inverse-limit lifts is substantial, so it was split into a named intermediate theorem.

## New nodes
`lem-weil-pbc-formal-annihilation-affine-limit-scalar` records the intermediate theorem.

## Second reading by R1

1. I compared the delivered target module with the repository version. The theorem signature is byte-for-byte unchanged; only proof imports and the proof body were added. Verdict: pass.
2. I compiled both delivered modules with `lcompile.py --all`. They compile without errors; the only remaining `sorry` is the explicitly named scalar-composite theorem. No forbidden declarations or hollow definitions were added. Verdict: pass.
3. The target proof uses the scalar-composite theorem and the public scalar-composite annihilation criterion. The added scalar theorem is a strictly simpler intermediate statement, with a source, docstring proof plan, and matching DAG node; it is not a restatement of the target. Verdict: pass.
4. The target statement and definitions are unchanged, and the affine-limit unit route is retained through the scalar-composite node. Verdict: pass.
5. Imports were checked for visibility: the two added imports are proof-only imports, while the existing public imports remain required by the target signature. The DAG proof and proof dependencies agree with the Lean proof. Verdict: pass.

Changed in this second reading: shortened the only overlong line in the new scalar module. No statements, definitions, proof route, or imports were otherwise changed.
