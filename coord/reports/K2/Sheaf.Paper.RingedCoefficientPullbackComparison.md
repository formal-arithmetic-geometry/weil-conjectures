## What changed

Proved `SheafOfModules.RingedCoefficientProjection.coefficientPullbackComparisons`,
with its original statement and public import preserved. Private proved helpers construct
ordinary comparison by restriction-of-scalars transport and iterated mates, then descend
its computation-normalized derived comparison from flat K-flat representatives.

Repaired the return at dd158ce46: removed the duplicate private theorems `iso_descent`
and `localization_iso_descent`. Added the proof-only import
`import all Sheaf.Paper.RingedProjectionPullbackComparisons` and applied the existing
`SheafOfModules.ProjectionCoherence.localization_iso_descent` directly. That theorem
already uses the existing `ProjectionCoherence.iso_descent`; neither proof is copied.
The import-direction check permits this dependency. The retained ordinary comparison,
K-flat preservation and representative normalization proofs are unchanged.

Updated the assigned node's proof, proof dependencies and proof origin to record this
reuse, preserving all other fields from the current repository node. The change record is
`coord/changes/K2-ringed-coefficient-pullback-comparison-proof-scope.md`.

## Proved and sorry left

Closed the one original hole in
`SheafOfModules.RingedCoefficientProjection.coefficientPullbackComparisons`
(`lem-pur-coefficient-pullback-comparison`). Holes closed: 1; holes added: 0.
No split-off statements and no `sorry` remain in the delivered Lean file.
The repaired file compiled through `lcompile.py` with no errors or warnings in
22.8 seconds. Delivery preflight checks the complete packet and its axioms.

## No longer needed

Removed the two duplicate private helper proofs identified by the return. The existing
`ProjectionCoherence.localization_iso_descent` supplies both descent steps. No modules
are withdrawn and no original imports are removed. The returned packet's direct
`Mathlib.CategoryTheory.Localization.Predicate` proof import is removed: the retained
proof now obtains the generic descent API from the existing comparison module. The
new proof-only import is required for that helper, including access to its private
declaration through `import all`.

The planned dependency `def-weil-presheaf-modules-sheafification` is not invoked directly:
normalized scalar adjunctions replace a fresh balanced-coequalizer construction. Resolving
localization uses the existing flat K-flat resolution theorem and the proved
`restriction_localization` helper, rather than the tensor-bifunctor clauses of the larger
site-derived-tensor descent theorem. Those modules may still be needed transitively;
no global pruning or unit-route change is claimed.

## Where the brief, the DAG or earlier work was wrong

The returned packet duplicated two already-proved generic descent helpers. This repair
imports and uses the existing theorem as requested. The earlier report's claim that
avoiding the source module justified locally repeating those proofs was incorrect.

The original ordinary proof plan was longer than necessary: graph transport gives the
restriction square, its underlying adjunction identifies the geometric mate as an
isomorphism, and Mathlib's iterated-mates theorem gives scalar-extension comparison.
The derived part follows the K-flat plan. No statement or definition repair was needed.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
