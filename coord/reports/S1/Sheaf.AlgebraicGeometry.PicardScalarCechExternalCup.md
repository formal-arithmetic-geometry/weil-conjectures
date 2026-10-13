## What changed
Added the main module proof as a direct application of a named core compatibility theorem. Added the core theorem in the same module with a documented sorry.

## Proved and sorry left
The target theorem `picardScalarCech_externalCup` is proved from `picardScalarCech_externalCup_core`. The core theorem remains sorry and is recorded by node `lem-sc-picard-scalar-cech-external-cup-core`.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The planned multi-page comparison argument was split into the core compatibility statement.

## New nodes
`lem-sc-picard-scalar-cech-external-cup-core` is the named core comparison obligation.

## Second reading by S1

1. Compared all delivered modules with the repository versions. Existing declaration signatures are unchanged; the only added declaration is the split pointwise core theorem recorded by the new node.
2. Compiled the sandbox module with `lcompile.py`; it compiles without errors. The target proof has no `sorry`; the split core theorem is the sole documented remaining `sorry`, with no hollow definition or forbidden declaration.
3. Checked the split statement against the target and edge cases (fixed degree and summand, including degree zero and empty-index cases). It is a pointwise instance of the compatibility assertion and is strictly smaller than the target's universal conclusion; its node has a non-circular proof dependency list.
4. The proof uses the existing component, comparison, Cech pullback compatibility, and scalar cohomology operation declarations. No imports were removed; no additional unused dependency was introduced.
5. The unit route is preserved: the external Cech component and scalar comparison steps remain explicit dependencies, and the unit record is untouched.

Changed the split theorem from a universal restatement to a pointwise compatibility obligation, updated its DAG proof and dependencies, and made the target proof introduce its quantified data before applying that pointwise theorem.
