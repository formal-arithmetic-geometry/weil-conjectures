## What changed

Added the proof-only import `Sheaf.AlgebraicGeometry.HigherDirectImageRawTransitionToHomCore` and proved the target theorem by evaluating the morphism-level coherence theorem at `z`. Added the new core module with its named intermediate theorem.

## Proved and sorry left

The target declaration `higherDirectImageRawTransition_toHom` is proved. The intermediate declaration `higherDirectImageRawTransition_toHom_core` remains `sorry`, recording the unresolved derived-adjunction coherence argument (node `sbc-lem-higher-image-raw-transition-to-hom-core`).

## No longer needed

No imports from the original module were removed; all remain part of the statement or the proof route.

## Where the brief, the DAG or earlier work was wrong

The DAG described the proof only at the pointwise level; the implementation requires the corresponding morphism-level coherence as an explicit intermediate theorem.

## New nodes

`sbc-lem-higher-image-raw-transition-to-hom-core` is added for the morphism-level coherence statement, in `dag/nodes/sec-smooth-base-change/sbc-lem-higher-image-raw-transition-to-hom-core.json`.

## Second reading by J1

1. I compared the delivered target module with the repository version. The target
   signature is unchanged byte for byte; only its proof imports the core theorem and
   applies `congrArg` at `z`.
2. Both modules compile locally. The target has no `sorry`; the only remaining hole is
   the explicitly named `higherDirectImageRawTransition_toHom_core`, with its matching
   node and source/docstring. No axioms, unsafe declarations, or hollow definitions
   were added.
3. The core statement is the morphism-level form of the target, with the same objects,
   hypotheses, coefficient map, and transition. Evaluating it at `z` gives exactly the
   target conclusion, so no hypothesis or conclusion was changed.
4. The proof route keeps the unit route: the existing transition, raw triangle pullback,
   and cohomology-presheaf modules remain imported; the core module is proof-only. No
   original import was removed because each remains needed by the statements or route.
5. I checked the new node and its Lean declaration agree, and checked the edge cases
   described by the declaration docstring (identity arrows, zero objects, and arbitrary
   integer degree). I removed the accidental duplicate root-level Lean file from the
   sandbox; it was not part of the delivery.

The target proof is therefore delivered as a reduction to the named morphism-level
coherence hole; no additional holes were introduced beyond that node.
