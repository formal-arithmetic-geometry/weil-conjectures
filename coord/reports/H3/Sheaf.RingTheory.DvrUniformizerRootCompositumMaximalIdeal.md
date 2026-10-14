## What changed

Added the proved Mathlib criterion `dvr_map_maximalIdeal_of_formallyUnramified`
and used it in the target theorem. The unresolved geometric argument is
isolated as `dvr_uniformizer_root_compositum_formallyUnramifiedData`.
Added the two corresponding DAG nodes and the proof-only import.

## Proved and sorry left

The target `RingTheory.dvr_uniformizer_root_compositum_map_maximalIdeal` is
proved from the two intermediate declarations. One sorry remains in
`RingTheory.dvr_uniformizer_root_compositum_formallyUnramifiedData`, node
`lem-sbc-dvr-uniformizer-root-compositum-formally-unramified-data`.
The generic criterion `RingTheory.dvr_map_maximalIdeal_of_formallyUnramified`
is fully proved from Mathlib.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The original plan compresses the construction of the formally unramified
normalization into one sentence. The missing construction is now a named,
strictly lower statement; the target proof and its final local algebra step
compile independently from it.

## New nodes

`lem-sbc-dvr-uniformizer-root-compositum-formally-unramified-data` is the
remaining normalization and ramification subproblem.
`lem-sbc-dvr-map-maximal-ideal-formally-unramified` records the proved local
criterion.

## Second reading by H3

1. Compared the delivered module with the repository version. Existing declaration signatures are
   unchanged; the target proof only supplies the previously missing argument and the added theorem
   is a strictly smaller intermediate result.
2. Compiled both delivered modules with `lcompile.py`; they compile successfully with no errors or
   warnings. The only remaining `sorry` is the named normalization theorem, and there are no
   forbidden declarations or hollow definitions.
3. Checked the split-off statement and its docstring against the stated Stacks Project route. It is
   true as the required formal-unramified and essential-finite-type subproblem, and is strictly
   weaker than the target. Its DAG node and Lean declaration agree.
4. The proof uses the Mathlib formally-unramified maximal-ideal criterion through a proof-only import;
   no shorter available route was found. The public imports are required by the theorem signatures,
   and no old proof dependency can be removed.
5. The target's unit route is preserved: the new intermediate node supplies the formal-unramified
   step, followed by the local maximal-ideal criterion. The unit and chapter metadata remain intact.

Changed the target proof to use `haveI` instances and wrapped the long application line to satisfy
style checks. No statements, definitions, or DAG routes were changed.
