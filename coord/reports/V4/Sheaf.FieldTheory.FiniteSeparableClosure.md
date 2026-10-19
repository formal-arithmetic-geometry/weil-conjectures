## What changed

Replaced the proof of `finite_separable_closure` in
`Sheaf.FieldTheory.FiniteSeparableClosure`, preserving its signature and imports.
For geometric irreducibility, apply
`AlgebraicGeometry.geometricallyIrreducible_iff_separableElements_mem` over
`separableClosure k K`. Mathlib's
`separableClosure.separableClosure_eq_bot` supplies the separable-permanence
argument already described in step 1 of the node. Membership in the bottom
intermediate field is precisely membership in the algebra map's range.
For finiteness, use `algebraicClosure.finite_of_fg`, include the separable closure
in the relative algebraic closure via `le_algebraicClosure`, and apply
`FiniteDimensional.of_injective` to that inclusion's linear map.

The proof follows Stacks 037Q and the existing DAG plan. No node, definition,
statement, visibility or public import changes.

## Proved and sorry left

Closed one hole: `finite_separable_closure`
(node `lem-zl-finite-separable-closure`). Zero holes remain in the item;
zero holes added and zero statements split off. This proves the item from its
stated dependencies, `algebraicClosure.finite_of_fg` and
`AlgebraicGeometry.geometricallyIrreducible_iff_separableElements_mem`, whose
existing holes are outside this delivery.

## No longer needed

None. Both proof imports are used. Both steps and all dependencies of the
existing DAG plan are retained; separable permanence is supplied by the proved
Mathlib relative-separable-closure theorem.

## Where the brief, the DAG or earlier work was wrong

None. Mathlib already packages the separable-permanence step in
`separableClosure.separableClosure_eq_bot`, so no auxiliary field construction
or new declaration is needed. Searches used LeanFinder for relative separable
closedness, Loogle for `separableClosure.separableClosure_eq_bot`, and ripgrep
in Mathlib and both project library roots. The proof applies unchanged to
trivial extensions, finite separable extensions, purely inseparable extensions,
and independent universes for the original fields.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
