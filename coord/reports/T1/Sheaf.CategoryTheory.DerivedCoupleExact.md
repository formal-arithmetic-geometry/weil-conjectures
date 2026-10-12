## What changed
Proved `pageCouple_image`'s final derived-E recurrence by definitional reduction, and reduced its remaining seven recursive image/inclusion clauses to the new `pageCouple_image_prefix` theorem. Added the proof-only import and module `Sheaf.CategoryTheory.PageCoupleImagePrefix`.

## Proved and sorry left
Closed the final recurrence clause of `CategoryTheory.BigradedExactCouple.pageCouple_image`. The seven recursive image/inclusion clauses are isolated in `CategoryTheory.BigradedExactCouple.pageCouple_image_prefix`, whose proof remains `sorry` (node `lem-sp-derived-couple-image-prefix`). The existing `derived_couple_exact` theorem remains proved.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The DAG's iteration step bundled the definitional derived-E recurrence with the substantially harder recursive image/inclusion induction; the former can be discharged by `rfl` once the latter is isolated.

## New nodes
`lem-sp-derived-couple-image-prefix`: the seven recursive image/inclusion clauses of `pageCouple_image`, sourced from Stacks 011S/0AMJ and the parent node's Step 11 induction; Lean module `Sheaf.CategoryTheory.PageCoupleImagePrefix`.

## Earlier second reading (a previous round; superseded)
A second reader should verify that the prefix is strictly weaker than `pageCouple_image` and that the final recurrence is definitional.

## Second reading by T1

1. Compared the delivered item module with the repository version. Existing theorem signatures and
   definitions are unchanged; the only existing proof change is the final recurrence of
   `pageCouple_image`. The split theorem has been moved into the item module without changing its
   statement.
2. Compiled all sandbox modules with `lcompile.py --all`; compilation succeeds. The only remaining
   `sorry` is the named split theorem `pageCouple_image_prefix`, and it has its DAG node and
   docstring. No definitions, axioms, unsafe declarations, or prohibited constructs were added.
3. Checked the split statement against the parent: it is exactly the seven recursive image/inclusion
   clauses and is strictly weaker than `pageCouple_image`, which additionally asserts the derived-E
   recurrence. The statement is needed to isolate the unresolved induction and is not duplicated in
   the library. The original separate module was removed because it could not prove its declared
   dependency on `derived_couple_exact` without an import cycle.
4. The parent proof now takes the shortest available route: apply the prefix theorem and close the
   final E recurrence by `rfl`. The existing proof-dependency imports remain necessary for
   `derived_couple_exact`; no imports can be pruned. The unit route and realized nodes are preserved.
5. Updated the prefix node's Lean location to the item module so its DAG record agrees with the
   declaration and proof dependency.

Changed during second reading: moved `pageCouple_image_prefix` from the separate proof-only module
into `DerivedCoupleExact.lean` to remove an impossible dependency cycle, removed that module from the
delivery, and updated the node location. The parent proof and remaining split are otherwise unchanged.
