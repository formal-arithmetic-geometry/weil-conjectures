## What changed

Proved the five theorems in `Sheaf.Paper.FieldDerivedScalarTower` without changing any
existing statement or definition. The existence and uniqueness proofs descend the
specified natural isomorphisms through the fully faithful precomposition functor for
localization at quasi-isomorphisms. Private normalization lemmas identify their selected
components. Associativity and the two unit identities follow by cancellation of the
factorizations, naturality, and the existing `ModuleCat.extendScalars_assoc`,
`extendScalars_comp_id`, and `extendScalars_id_comp` identities, degree by degree.
Shift compatibility is detected after precomposition with Q, where the comparisons are
composites of the shift-compatible termwise and localization factorization maps.
The unit shift proof explicitly inserts the canonical left unitor of Q between the
whiskered complex identity comparison and the inverse right unitor; this connects
the composite shift structures correctly.

Added the proof-only import
`WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Shift` for its existing shift
instances and the criterion detecting shift compatibility after essentially surjective
precomposition. The original eight-step DAG route and all five declared dependencies
remain in use; the unit has no realized proof steps to bypass.

## Proved and sorry left

Closed all five original holes:

- `DerivedCategory.existsUnique_fieldScalarTower`.
- `DerivedCategory.existsUnique_fieldScalarUnit`.
- `DerivedCategory.fieldScalarTower_assoc`.
- `DerivedCategory.fieldScalarTower_units`.
- `DerivedCategory.fieldScalarTower_commShift`.

All realize `lem-weil-derived-field-scalar-extension-tower`. No holes added, no holes
left in the delivered module, and no split-offs. Existing signatures and visibility
are unchanged. This is a proof, not a decomposition.

## No longer needed

None. No imports, declared proof dependencies, nodes, or modules are pruned.
The construction uses the existing localization API directly, as the node prescribes.

## Where the brief, the DAG or earlier work was wrong

No mathematical errors found. The library's tensor convention puts the extended scalar
on the left; the existing `ModuleCat` comparison identities supply precisely the
component equations needed in that convention. The source-library search found generic
shift detection and termwise shift instances, which avoid redoing the shift calculation.
The retained attempt had unfinished unit simplifications and omitted the left-unitor
bridge needed by shift instance synthesis. Both are repaired. The final module compiled
cleanly through `lcompile.py` in 5.1 seconds, with no warnings. No existing statements,
definitions, docstrings, or visibility changed.

Delivery infrastructure: the required dry run reached worktree admission, then
`deliver3.py` crashed in `sharedrepo.worktree` because its
`git checkout -q --detach origin/sheaf-dag` exceeded the tool's 600-second timeout.
The supplied command was retried unchanged; no launcher scripts were modified.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
