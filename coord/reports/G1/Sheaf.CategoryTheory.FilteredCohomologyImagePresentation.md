## What changed

Proved `CategoryTheory.DecreasingFiltration.cohomologyImage_graded_presentation` by composing
an intermediate normalized quotient presentation with the existing
`normalizedStationaryQuotient_presentation`. Added the proof-only import
`Sheaf.CategoryTheory.FilteredCohomologyImageNormalized`. The intermediate result is stated
in a new module and remains `sorry`, with its own DAG node.

## Proved and sorry left

Closed the original hole `cohomologyImage_graded_presentation` in node
`lem-sp-filtered-cohomology-image-presentation`. Added the strictly smaller named theorem
`cohomologyImage_graded_normalized` in node
`lem-sp-filtered-cohomology-image-normalized-quotient`; its proof remains `sorry` and is the
single split-off hole. The final proof is a genuine composition of the two isomorphisms.

## No longer needed

No imports were removed. The direct multi-step categorical argument in the original node is
replaced by the normalized quotient theorem and the existing normalized stationary quotient
presentation. No existing node or module is claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan omitted the normalized quotient interface already present in
`FilteredNormalizedQuotientPresentation`; exposing the required intermediate comparison makes
the composition compile. No target statement or existing definition was changed.

## Earlier second reading (a previous round; superseded)

The item signature is unchanged. The target proof compiles and uses the intermediate theorem
only to produce the normalized cokernel and then applies the existing theorem. The new theorem
has fewer conclusions than the target and is strictly an intermediate quotient statement.
The node records and module imports match the delivered declarations.

## New nodes

`lem-sp-filtered-cohomology-image-normalized-quotient` is added at
`dag/nodes/sec-abelian-varieties/lem-sp-filtered-cohomology-image-normalized-quotient.json`.

## Second reading by G1

1. **Interface unchanged.** Compared the delivered presentation module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only proof-only imports and the proof body changed. Verdict: pass.

2. **Proof and axioms.** Compiled both delivered modules with `lcompile.py --all`. The target proof is the composition of the normalized presentation isomorphism with `normalizedStationaryQuotient_presentation`; no forbidden declarations or hollow definitions were introduced. The remaining `sorryAx` comes only from the explicitly split theorem and existing imported theorem. Verdict: pass.

3. **Split-off statement.** Checked `cohomologyImage_graded_normalized` against the normalized quotient construction. It is a strictly smaller intermediate result: it supplies the containment and identifies the graded image with the normalized cokernel, without restating the target's final cycle presentation. Its docstring gives the source and proof argument, and its DAG node matches its Lean statement. Verdict: pass.

4. **Pruning and imports.** The normalized quotient and intermediate modules are required by the proof. The first is imported privately because it is proof-only; the public filtered cohomology import remains required by the target statement. No old proof dependency can be removed without changing the planned route, and no module is falsely claimed pruned. Verdict: pass.

5. **DAG and unit route.** The target node records the new composition route, and the new normalized quotient node records the split theorem, source, dependencies, and Lean declaration. The route still uses the existing normalized stationary quotient interface and does not alter any unit statement. Verdict: pass.

Changed after this reading: added this review section only; no Lean declarations or DAG statements were changed.
