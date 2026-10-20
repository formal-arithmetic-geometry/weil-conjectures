## What changed

Withdrew `Sheaf.Algebra.Homology.ZigzagBoundaryReduction`, an unused duplicate of the
adopted source-library module `WeilConjectures.Algebra.Homology.ZigzagBoundaryReduction`.
Redirected node `new-zigzag-boundary-reduction` to the existing proved theorem
`HomologicalComplex₂.zigzagBoundary_reduction`. Its signature differs from the retired
`HomologicalComplex₂.zigzag_boundary_reduction` only in the theorem name. Its proof is the
same two-step lifting and subtraction argument, so the node's proof dependencies stay.
No source-library file changes and no consumer adaptations.

Verified with lcompile.py that a theorem with the complete old signature is proved directly
by `zigzagBoundary_reduction A hrow n a ha hboundary` (compiled in 1.4 seconds). The canonical
theorem's `#print axioms` reports exactly propext, Classical.choice and Quot.sound.
This verification file was removed from the sandbox before delivery.

Change record: `coord/changes/retire-zigzag-boundary-reduction.md`.

## Proved and sorry left

The assigned module already had zero holes. Closed: 0; added: 0; remaining: 0.
No new theorem or split-off result is introduced. Retired the duplicate proved declaration
`HomologicalComplex₂.zigzag_boundary_reduction`; the same result remains proved by
`HomologicalComplex₂.zigzagBoundary_reduction`, node `new-zigzag-boundary-reduction`.
This is duplicate retirement, not a newly closed proof hole.

## No longer needed

Pruned module `Sheaf.Algebra.Homology.ZigzagBoundaryReduction` and its duplicate declaration.
The downstream.py check reports zero downstream modules and only the old declaration itself
as a use of its name. Repository-wide rg confirms no other uses or imports.
Existing consumers use the canonical source-library module already. The DAG node is retained
and attached to the canonical theorem; no mathematical dependency is pruned.

Withdrawal removes this unused module's imports of:

- `WeilConjectures.Algebra.Homology.ZigzagModule`;
- `Mathlib.Algebra.Homology.HomologicalComplexAbelian`;
- `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`;
- `WeilConjectures.Algebra.Homology.ZigzagModuleFunctorial`;
- `Mathlib.Algebra.Category.ModuleCat.Abelian`;
- `WeilConjectures.Algebra.Homology.ZigzagToRowCokernel`.

These dependencies remain needed by the canonical proof and are not withdrawn.
The unit route is unchanged: this node realizes no unit statement or unit proof step.

## Where the brief, the DAG or earlier work was wrong

The item is already proved and has an adopted source-library twin. The old DAG attachment
still pointed to the Sheaf duplicate despite its lean_audit already naming the closed upstream
theorem. The retirement census deferred it because a consumer was in a pending landing; no
such consumer obstruction remains in the current tree. Brief step 8d authorizes withdrawing
an unused item rather than retaining a duplicate proof.

Searches: msearch.py leanfinder for lifting a row-cokernel boundary returned general homology
boundary lemmas, with no direct Mathlib replacement; loogle for zigzagBoundary found no hit;
msearch.py grep likewise found no hit. Repository rg found the exact canonical theorem and
no users of the old Sheaf name. The canonical theorem was read in full, and its statement
match and allowed axioms were checked by Lean. Stacks algebra.tex Tag 00M1's injectivity
paragraph (lines 18488--18504) supplies the unchanged mathematical argument.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
