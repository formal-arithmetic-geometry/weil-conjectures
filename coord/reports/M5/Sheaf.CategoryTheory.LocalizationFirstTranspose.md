## What changed

Proved `CategoryTheory.localization_first_transpose` in
`Sheaf.CategoryTheory.LocalizationFirstTranspose`, keeping its statement and public imports
unchanged. Mathlib's `complete_distinguished_triangle_morphism₁` supplies the rotated TR3
completion with the prescribed middle and third components. The mapped source triangle is
distinguished by `SX.map_distinguished`; `isIso₁_of_isIso₂₃` proves the first component invertible.
For every counit-normalized map, fullness of `IB` and `Adjunction.eq_unit_comp_map_iff` identify
its preimage with the prescribed adjunct. Mapping that equality proves the transpose formula;
cancellation of the comparison isomorphism proves uniqueness.

The proof follows the node's three existing steps and dependencies, so no DAG change is needed.
No definitions or other modules were changed. Compilation through `lcompile.py` succeeded after removing the redundant import.
`#print axioms` reported exactly `propext`, `Classical.choice`, and `Quot.sound`; the
temporary diagnostic command was then removed.

## Proved and sorry left

Closed one hole: `CategoryTheory.localization_first_transpose`
(node `lem-coef-localization-first-transpose`). Added zero holes; zero sorries remain in the
item or elsewhere in this delivery. No statements were split off.

## No longer needed

Removed the redundant private import `Mathlib.CategoryTheory.Adjunction.Basic`: it is already
publicly imported by `Mathlib.CategoryTheory.Adjunction.Mates`.
All three planned proof dependencies remain used through their Mathlib declarations:
`def-weil-triangulated-category`, `lem-sf-triangle-morphism-iso`, and
`lem-weil-pbc-adjunct-counit-identity`. No DAG nodes or modules are pruned, and no unit route
is bypassed. The unit's `realized` statement and step lists are empty.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error was found. Mathlib already packages the rotation,
shift-preimage and sign argument in `complete_distinguished_triangle_morphism₁`, so no manual
reimplementation of that step was necessary. The current snapshot places the unit section in
`sec-six-functors-basics`; the node's cited older finite-closed-shriek source is available in
the master snapshot and was read there.

## Second reading by M5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
