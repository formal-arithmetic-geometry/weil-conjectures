## What changed
Added proof-only import of `SeparatedAffineFunctionFieldSurjectiveCore` and reduced the target to the affine-spectrum closed-immersion criterion. Added the core module with the geometric closed-immersion statement and a generic affine-spectrum surjectivity bridge.

## Proved and sorry left
The target theorem `Scheme.separated_affine_functionField_surjective` is proved by applying the named geometric intermediate theorem and the affine-spectrum criterion. A sorry remains only in `Scheme.isClosedImmersion_specMap_tensor_functionField` in the new core module; the generic affine-spectrum surjectivity bridge is proved from Mathlib's affine closed-immersion criterion.

## No longer needed
No imports were removed; the original planned dependencies remain available for the core geometric step.

## Where the brief, the DAG or earlier work was wrong
The planned geometric and affine steps had no Lean declarations in the import closure, so they were split into explicit intermediate statements.

## New nodes
`lem-sc-separated-affine-function-field-surjective-core` records the closed-immersion intermediate statement and its module.

## Second reading by R1

1. Compared the delivered target module with the repository version. The target signature and all existing declarations are byte-for-byte unchanged; the only target change is the proof and its proof-only import.
2. Compiled both delivered modules with `lcompile.py --all`. There are no errors, forbidden declarations, or sorries in the target module. The only remaining sorry is the named geometric theorem in the core module, and its docstring and DAG node are present. The target's axioms reduce to the permitted axioms plus the open geometric theorem.
3. Checked the split statement against the separated affine function-field argument and searched the library and Mathlib for existing declarations. The split theorem is the required closed-immersion reduction and is neither a restatement of the target nor duplicated elsewhere. The generic surjectivity bridge is now proved directly using `IsClosedImmersion.isAffine_surjective_of_isAffine` and the canonical spectrum global-sections isomorphisms.
4. The proof follows the planned unit route: the target reduces through the closed-immersion statement, then through the affine-spectrum criterion. No route-changing imports were introduced; the core import is proof-only in the target module.
5. The DAG node's Lean declaration, proof dependencies, source, and proof origin agree with the delivered core theorem. No new node was needed after closing the generic bridge.

Changed the core proof to close `surjective_of_isClosedImmersion_specMap`; updated the report to record that only the geometric theorem remains open.
