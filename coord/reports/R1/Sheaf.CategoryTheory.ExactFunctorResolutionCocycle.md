## What changed

Added the integer-indexed comparison construction and its degreewise commutation proof. The target theorem is now proved from the named derived-category hom equality intermediate theorem.

## Proved and sorry left

`exactFunctor_resolution_cocycle` is proved. `exactFunctor_resolution_cocycle_hom` remains as a named `sorry` intermediate theorem, with node `lem-weil-pbc-exact-functor-resolution-cocycle-hom`.

## No longer needed

No imports or stated dependencies were removed; the Mathlib imports remain needed for the Ext and derived-category APIs.

## Where the brief, the DAG or earlier work was wrong

The DAG plan omits the substantial integer-indexed extension and derived-category representative calculation. This delivery isolates that calculation as a strictly lower hom-level statement.

## New nodes

`lem-weil-pbc-exact-functor-resolution-cocycle-hom` records the derived-category hom equality used to prove the Ext equality.

## Earlier second reading (a previous round; superseded)

The item theorem has the original signature and is proved by `Abelian.Ext.ext` from the strictly lower hom-level statement. The comparison extension is degreewise checked, including negative degrees via zero objects. The new node records exactly the hom equality and keeps the blueprint route.

## Second reading by R1

1. I compared the delivered module with the repository version. The existing target declaration has the same
   signature byte for byte; the only added declaration is the named lower hom equality recorded by the new node.
   Verdict: passed.
2. I compiled the module with `lcompile.py`. The file has no forbidden commands and no `sorry` in a definition;
   the remaining `sorry` is exactly the named intermediate theorem listed above. The target proof uses
   `Abelian.Ext.ext` and the intermediate hom equality, so its only additional axiom while that statement is open
   is `sorryAx`. Verdict: passed subject to the declared split theorem.
3. The split-off hom equality is a true specialization of the derived-category representative calculation and is
   strictly stronger at the morphism level than the Ext equality, hence a valid lower statement. Its source,
   proof route, node, and docstring are present, and it is not duplicated by the searched Mathlib or library APIs.
   Verdict: passed.
4. The proof follows the resolution-comparison route: the comparison is extended by zero to integer complexes,
   with the negative-degree commutation discharged using zero objects. Both imports occur in public signatures and
   remain necessary; no old dependency was removed. Verdict: passed.
5. The new node's Lean declaration and statement match the module exactly, and its proof dependency is the
   injective-resolution construction used by the extension. The unit route remains the resolution cocycle route.
   Verdict: passed.

I changed only the report by adding this review record. No Lean statement or proof was changed during second
reading; the lower theorem remains intentionally split off with its documented source and node.
