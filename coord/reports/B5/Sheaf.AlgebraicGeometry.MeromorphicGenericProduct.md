## What changed

Replaced the sorry in `meromorphicModule_generic_product` by the canonical fraction-to-generic-factor construction, restriction compatibility, extension across sheafification, affine-basis gluing, unit-stalk identification, and the tensor comparison. The original signature and public imports are unchanged.

Repair of the return on delivery `9d06ff05c60`: removed the private duplicate
`meromorphicRestriction_mk`. Both restriction calculations now use
`(exists_meromorphicRestriction X M i).choose_spec` from the already imported
`Sheaf.AlgebraicGeometry.MeromorphicModule` directly. The matching formula there is
private; its public existence theorem supplies exactly the same fraction formula
without exporting or restating a declaration. Compared the retained item with the
current shared source: its theorem signature and public imports still match.

Added `Sheaf.AlgebraicGeometry.MeromorphicGenericAffine` with the affine section calculation from the proof of Stacks Tag 0EMF. Its hypothesis normalizes a linear map on m/1; it concludes only that one affine component is invertible. The original theorem constructs that map, proves the normalization, glues, identifies the scalar factors and proves the tensor clause. No definitions use unproved arbitrary witnesses.

Validation of the repair: `MeromorphicGenericAffine` compiles with lcompile.py,
and the repaired item compiles against it in 39.3 seconds. The exact
`tools/import_prune_check.py` check that rejected the old packet now passes. Edge cases checked mathematically: empty affine open/zero ring, zero module, generic points outside the open, infinitely many global components but finitely many in each affine, and nonreduced generic local rings. The new affine statement permits these cases.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.Scheme.Modules.meromorphicModule_generic_product` (node `lem-sc-meromorphic-weakass-generic-product`), from one new affine lemma. Added one hole: `AlgebraicGeometry.Scheme.Modules.meromorphic_affine_generic_sections_isIso` (node `lem-sc-meromorphic-affine-generic-sections`). Thus the item has zero sorries, the new module has one, and this delivery is a decomposition with net zero holes closed, not a complete proof of the import closure.

The tensor comparison is proved independently of the new lemma for every module. The fraction-map, gluing and unit normalization helpers are complete proofs. The remaining affine calculation requires the finite minimal-prime ring decomposition, weak-association localization and the affine quasi-coherent stalk comparisons; its docstring and node give the argument.

## No longer needed

Removed private imports `Sheaf.AlgebraicGeometry.TotalQuotientRingMinimalProduct` and `Sheaf.RingTheory.WeakAssZeroDivisors` from the item: the outer proof uses the new affine lemma instead. Removed the duplicate private helper `meromorphicRestriction_mk`; the existing public
`exists_meromorphicRestriction` supplies its two proof uses. No module is withdrawn. The total-quotient dependency remains in the affine node's plan; it is not globally pruned. The zero-divisor union node `lem-sc-affine-weakass-nonzerodivisors` is unnecessary for the new plan because the total-quotient theorem now proves the required implication directly. Its module is not imported by this packet.

## Where the brief, the DAG or earlier work was wrong

The returned packet unnecessarily restated a private formula already supplied by
`exists_meromorphicRestriction`; the repair reuses that public theorem directly.

The planned algebra decomposition now has a proved Lean body in the shared tree. The missing work is the affine geometric comparison and finite-module tensor calculation, not an unavailable total-quotient declaration. The previously stated `meromorphicModule_tensor_iso` assumes invertibility; the required arbitrary-module tensor comparison was proved directly rather than treating that stronger assumption as available.

## New nodes

`lem-sc-meromorphic-affine-generic-sections` isolates the affine calculation in Stacks Tag 0EMF. It is strictly smaller than the original global statement: one affine component, local finiteness only, no sheafification, no restriction gluing, no scalar-factor normalization and no sheaf tensor comparison. LeanSearch, LeanFinder and source grep found no existing theorem with that statement; the whole-blueprint search for "meromorphic affine" found no match. The proof-context commands are recorded in `coord/changes/B5-meromorphic-generic-proof-context.md`; no existing statement, definition or public import was changed.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
