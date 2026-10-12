## What changed

Added the proof-only module `Sheaf.RingTheory.CyclicGlobalDimension` with the intermediate theorem `Ring.hasGlobalDimensionLE_of_cyclic`, and used it to prove `Ring.hasGlobalDimensionLE_iff_finite_iff_cyclic`. Imported `Mathlib.RingTheory.Finiteness.Basic` for the finite quotient instance.

## Proved and sorry left

The target theorem is reduced to the named intermediate theorem. The declaration `Ring.hasGlobalDimensionLE_of_cyclic` in `Sheaf.RingTheory.CyclicGlobalDimension` remains `sorry` and has node `lem-weil-pbc-global-dimension-finite-modules-suffice-cyclic-to-global`. The change record is `coord/changes/finite-basic-import.md`.

## No longer needed

No planned imports were removed. The well-ordered union module remains part of the stated route.

## Where the brief, the DAG or earlier work was wrong

The cyclic-to-global filtration argument was too large to complete in this session, so it was split into a strictly smaller intermediate theorem.

## New nodes

`lem-weil-pbc-global-dimension-finite-modules-suffice-cyclic-to-global` records the cyclic-to-global filtration argument and its source in Stacks Tag 065T.

## Earlier second reading (a previous round; superseded)

The target signature is unchanged and compiles. The finite-to-cyclic direction uses the standard finite quotient instance; the reverse direction and global conclusion are isolated in the strictly smaller cyclic-to-global theorem. The new node records the exact remaining proof obligation and its Stacks source.

## Second reading by Q3

1. I compared the delivered target module with the repository version. The theorem signature
   of `Ring.hasGlobalDimensionLE_iff_finite_iff_cyclic` is unchanged byte for byte; only its
   proof and a proof-only import were changed. The newly added cyclic theorem has the statement
   recorded by its new DAG node.
2. Both delivered Lean modules compile with `lcompile.py --all`. The target proof has no
   `sorry`; the only remaining `sorry` is the named theorem
   `Ring.hasGlobalDimensionLE_of_cyclic`, with its split node and a complete proof plan in
   its docstring. No forbidden declarations or hollow definitions were introduced.
3. The target proof uses the finite quotient instance from
   `Mathlib.RingTheory.Finiteness.Basic`; this is a plain proof-only import. The existing
   public imports and the well-ordered-union route remain in place. The existing DAG node was
   restored unchanged; the new node records the split theorem and its proof dependency route.
4. The finite-to-cyclic direction is proved by the standard finite quotient instance, while the
   cyclic-to-global filtration is honestly split off because the required well-ordered
   filtration proof is not yet present. No target statement or definition was changed.
5. The unit route is preserved: the target still uses the well-ordered-union projective
   dimension theorem, and the new split node is below the unit level. The new statement is
   strictly smaller than the target and is exactly the unresolved cyclic-to-global implication.

Changes made during this second reading: restored the pre-existing target DAG node verbatim,
expanded the split theorem's proof docstring, and added this review section.
