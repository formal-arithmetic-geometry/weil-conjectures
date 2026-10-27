## What changed

Proved `SheafOfModules.FlatSingleDerivedNormalization.flat_single_derived_normalization`
in `Sheaf.Algebra.Homology.FlatSingleDerivedNormalization`, preserving its exact statement,
both existing abbreviations and every public import.

The proof transports exactness along `siteSheafTensorRightIso`, proves that zero objects
and all terms of the degree-zero single complex are flat, and proves K-flatness by exactness
and the existing collapse isomorphism. Its collapse calculation and integer-shift square
are proved for a generic additive bifunctor before specializing to sheaves, avoiding expensive
unfolding of the sheaf tensor instance.

The existing fixed K-flat tensor theorem supplies the triangulated structure and normalized
comparison on every complex. `Localization.liftNatIso` constructs the comparison with
termwise derived tensor. Its shift compatibility follows by precomposition with localization
and essential surjectivity. A second explicit natural isomorphism, using
`ShortComplex.mapHomologyIso`, descends the cohomology comparison with exactly the required
representative value. Every helper is private and fully proved.

Added the proof-only import `WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift`.
Updated the existing node's first proof step and proof dependency to name the independent
coefficient site tensor comparison actually used. The eight-step mathematical route is kept;
no unit statement or step changes. The unit record `sk-prop-an` has no realization attached
to this node.

Validation: the final module compiled without errors or warnings using `lcompile.py`
(43.3 seconds). Import-direction checking permits the new proof import. No new statements,
definitions or modules are exposed publicly. The conservative interface-command gate also
requires a record for the variables scoped to the private generic helpers:
`coord/changes/flat-single-derived-normalization-private-helpers.md`. Its consumer search
found zero downstream modules, so no adaptations are needed.

## Proved and sorry left

Closed 1 original hole:
`SheafOfModules.FlatSingleDerivedNormalization.flat_single_derived_normalization`
(node `lem-pur-flat-single-derived-normalization`).

Zero holes remain in the item. Zero holes were added; zero statements were split off.
This is a proof from the existing declared dependencies, rather than a decomposition.

## No longer needed

Removed the direct proof import
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`.
The proof uses the canonical tensor's existing additive instances and the independent
coefficient site tensor comparison; it does not use tensor closedness or internal Hom.
Accordingly, `lem-pc-sheaf-modules-tensor-closed` is replaced by
`lem-weil-pbc-independent-sheaf-tensor-colimits` in the first proof step and `proof_deps`.
The former remains a statement dependency in the unchanged mathematical statement.
No module is withdrawn and no whole-library pruning is claimed. All other declared
proof dependencies remain used by the stated route.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or source error was found. The first proof step named the
same-universe tensor-closed wrapper; the independent-coefficient `siteSheafTensorRightIso`
is the applicable exactness comparison in the given universe-general setting.
The source-library boundary is respected: no file under `WeilConjectures` is changed.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
