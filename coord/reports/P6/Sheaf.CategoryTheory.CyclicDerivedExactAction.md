## What changed

Proved `CategoryTheory.Endofunctor.IsoAlgebra.cyclicDerivedHomTransport_exact_action`
in `Sheaf.CategoryTheory.CyclicDerivedExactAction`, following the existing node's
three-step argument. Private helpers compute the canonical comparisons on complexes,
localize the fixed-pair structure square, and establish the abstract conjugation
identity using naturality and shift compatibility. The proof imports
`WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor` and
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate` privately.
All existing public signatures, definitions and public imports are preserved.
The item node records the same three-step route with the actual helper and API names.

## Proved and sorry left

Closed the sole original hole in
`CategoryTheory.Endofunctor.IsoAlgebra.cyclicDerivedHomTransport_exact_action`
(node `lem-sf-cyclic-derived-exact-action`). No holes added, no split-off statements,
and no `sorry` remains in the delivered module. All private helpers are proved.

Validation: the module compiles without warnings through `lcompile.py` in 8.6 seconds.
The original public theorem signature was checked verbatim against the source.

## No longer needed

None. The proof uses all three existing dependencies:
`def-sf-cyclic-derived-hom-data`, `def-weil-endofunctor-fixed-pair-category`, and
`lem-sf-exact-functor-derived-triangulated`. No imports, modules or nodes are pruned.
No boundedness, resolution, or Grothendieck hypothesis is needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was required. The shift-compatibility argument is
already proved by the instances in
`WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor`.
The existing node's proof route and dependencies therefore remain accurate.

## Second reading by P6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
