## What changed

Proved `AlgebraicGeometry.isProper_of_fpqc_cover` in
`Sheaf.AlgebraicGeometry.ProperMorphismFpqcDescent` without changing its signature,
universes, visibility or public imports. The proof specializes the existing closed theorem
`Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology` to properness, using the existing closed
`isProper_descendsAlong_surjective_inf_flat_inf_quasiCompact` instance. The covering presieve
generates the required covering sieve, and `IsPullback.of_hasPullback` supplies every square.

Added only proof imports of `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc` and
`WeilConjectures.AlgebraicGeometry.FieldExtensionDescent`. Updated the proof docstring and the
item node's proof, proof dependencies and origin to the actual shorter route. Added a node
attaching the already proved single-morphism properness instance; no Lean declaration was added.
The existing generic family theorem already has node
`lem-weil-pbc-fpqc-family-descent-of-single-morphism-descent`.

The item is below the compact-support base-change unit. Its unit's `realized` statement and
steps lists are empty, and no fixed unit carrier or chapter route is bypassed. The existing
closed generic tool applies to arbitrary covering families and index universes, including an
empty family over an empty scheme.

Validation: the item compiled through `lcompile.py` in 1.8 seconds. A separate scratch copy
with `#print axioms AlgebraicGeometry.isProper_of_fpqc_cover` compiled in 2.8 seconds and
reported exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Proved and sorry left

Closed 1 of 1 original holes: `AlgebraicGeometry.isProper_of_fpqc_cover`
(node `lem-weil-pbc-proper-morphism-fpqc-descent`).

No `sorry` remains in the item. Added 0 holes and split off 0 obligations.
The new DAG attachment points to an existing closed source-library instance, not a new hole.
The axiom check confirms the resulting theorem has no transitive `sorryAx` dependency.

## No longer needed

Removed these proof imports from this module:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed`
- `Mathlib.CategoryTheory.Sites.Precoverage`
- `Sheaf.AlgebraicGeometry.UniversallyClosedOfFpqcCover`
- `Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeOfFpqcCover`
- `WeilConjectures.AlgebraicGeometry.OverPullbackDiagonalClosedImmersion`
- `Sheaf.AlgebraicGeometry.FpqcClosedImmersionDescent`

The new proof does not directly use these old planned dependencies:
`def-weil-finite-type-morphism`, `lem-weil-pbc-fpqc-descend-universally-closed`,
`lem-weil-pbc-fpqc-descend-locally-finite-type`,
`lem-weil-pbc-universally-closed-quasi-compact`,
`lem-galois-fpqc-covering-base-change`,
`lem-weil-pbc-over-pullback-diagonal-closed-immersion`, and
`lem-pc-fpqc-descend-closed-immersion`.
The first notion still occurs in the new closed instance node's statement. No claim is made
that these nodes or modules are unused by other parents. The source proof already supplies
the single-morphism descent, and the generic theorem handles the passage to a covering family,
so this item needs no separate family descent of its constituent properties or diagonal.

Pruned all four obsolete top-level `tool_uses` approvals from the item node:
`lem-weil-pbc-fpqc-descend-universally-closed`,
`lem-weil-pbc-fpqc-descend-locally-finite-type`,
`lem-weil-pbc-over-pullback-diagonal-closed-immersion`, and
`lem-pc-fpqc-descend-closed-immersion`. No approval was added or reordered.

## Where the brief, the DAG or earlier work was wrong

The six-step plan is mathematically valid, but the source library already proves both
single-morphism properness descent and generic covering-family descent. Their specialization
closes the obligation with only standard axioms, so the longer explicit diagonal route is
unnecessary here. Mathlib-only search missed this combination in the source library.
No statement, definition, target or consumer required repair. No forced adaptations.

## New nodes

`lem-weil-pbc-proper-single-fpqc-descent` attaches the already proved
`AlgebraicGeometry.isProper_descendsAlong_surjective_inf_flat_inf_quasiCompact`
in `WeilConjectures.AlgebraicGeometry.FieldExtensionDescent`. It states descent along one
surjective flat quasi-compact morphism and supplies the single-morphism hypothesis of the
existing generic family theorem. Its source is Stacks Descent Tag 02L1; its full proof is the
existing intersection-descent proof after `isProper_eq`, using diagonal descent for
separatedness. LeanSearch, Loogle and source/DAG grep were performed. No new Lean module,
new declaration, change record or unproved obligation is introduced.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
