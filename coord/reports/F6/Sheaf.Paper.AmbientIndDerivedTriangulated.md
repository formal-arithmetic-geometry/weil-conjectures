## What changed

Proved both declarations in `Sheaf.Paper.AmbientIndDerivedTriangulated` without changing
any existing signature or definition. Four proved private helpers construct the zero
finite constant local model and singleton stratification, handle the affine-local branch,
and package the stated ind-heart kernel/cokernel and extension results as weak Serre
class instances. Applied the existing proved library theorem
`DerivedCategory.homologyProperty_isTriangulated`; the separate repleteness theorem
transports each cohomology object along the image of the derived isomorphism.

Added the proof-only import
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty`.
Updated the existing node's proof, proof dependencies and proof origin to this route.
The unit's cohomology/kernel/cokernel/extension argument is retained, including both
canonical coefficient rings and all integer degrees. No new modules, nodes, definition
repairs, signature changes, or forced adaptations.

The zero construction works for arbitrary commutative condensed coefficients, including
the zero coefficient ring, and on the empty scheme. It treats both the qcqs and
affine-local branches directly. Local Noetherianity and compactness required by the
extension lemmas follow from the existing geometric hypotheses.

Validation: remote single-file compilation passed. Axiom inspection of the isomorphism
closure theorem returned only `propext`, `Classical.choice`, and `Quot.sound`. The
triangulated theorem additionally retains `sorryAx` from the already stated ind-heart
dependencies; no new axiom or hole was introduced. The unchanged characteristic
parameters of the separate repleteness theorem are mathematically unused and retained
verbatim.
The existing generic library theorem was read in full; it is proved and constructs the
required cokernel/kernel short exact sequence, so the argument is not a new assumption.
Searches used leanfinder, loogle, the launcher grep service, and source ripgrep before
choosing this shorter route.

## Proved and sorry left

Closed 2 of 2 existing holes, both on `det-ambient-ind-derived-triangulated`:

- `AlgebraicGeometry.ProEtale.indConstructibleDerived_isTriangulated`.
- `AlgebraicGeometry.ProEtale.indConstructibleDerived_isClosedUnderIsomorphisms`.

Added 0 holes; split off 0 statements. No sorry remains in any delivered Lean file.
The triangulated theorem uses the already stated `indHeart_kernelsCokernels`,
`indConstructible_of_shortExact`, and `indConstructible_of_shortExact_padicAlgCl`;
their existing proof obligations remain with their own modules.

## No longer needed

Removed the redundant direct proof imports:

- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
- `Mathlib.CategoryTheory.Shift.ShiftSequence`.
- `Mathlib.CategoryTheory.Abelian.Basic`.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`.

These Mathlib modules remain available through the generic HomologyProperty API;
this delivery does not claim that they leave the transitive import closure.

Removed these explicit proof dependencies from the item's node, since the proved generic
weak Serre class theorem supplies their homological-algebra work:
`lem-sp-derived-cohomology-shift`, `lem-sf-derived-homology-long-exact`,
`pur713-def-module-category`, `def-sp-abelian`, `lem-weil-pbc-coimage-mono`, and
`def-weil-triangulated-category`. None requires a separate new proof for this item.
The closed node `prop-constructible-derived-subcategory` already records the general
`DerivedCategory.homologyProperty_isTriangulated` declaration, so it is reused.
The supplied ind-heart kernel/cokernel and extension modules remain needed.
No project module is asserted to be globally pruned.

## Where the brief, the DAG or earlier work was wrong

The DAG's repeated searches missed the proved source-library weak Serre class API in
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty`.
Its application avoids repeating the long exact sequence and opposite-category image
argument in this module. The mathematical statement and the unit-level route were correct.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
