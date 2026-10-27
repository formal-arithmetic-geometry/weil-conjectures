## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_isAmple_on_affineOpens_comp` in
`Sheaf.AlgebraicGeometry.QuasiprojectiveQCComposition`, with its signature unchanged.
Added private imports of `CompositionFiniteAffineTwistBounds` and
`InvertibleTwistOpenRestriction`. The existing finite-cover bounds give the composite's
finite type and quasi-compactness. Sum the nonnegative local integer bounds to obtain
one common exponent; form the actual global tensor twist, transport the local
ampleness along the existing restriction comparison, and apply
`scheme_relative_ample_affine_cover`. The empty sum gives exponent zero on an empty
cover. No object is chosen from a mere unproved existence theorem: only integer bounds
and the invertible modules supplied as hypotheses are selected.

Updated Step 2 and the proof-origin note of
`lem-sfb-quasiprojective-qc-composition` to record the sum instead of the maximum.
All three existing proof dependencies are used; the unit route is preserved.
LeanFinder returned composition/permanence results, Loogle returned no `IsAmple`
match, and Mathlib/source-library searches found no shorter relative-ampleness
composition theorem. The source argument was checked in Stacks 0C4K, 0C4M and 01VJ.

## Proved and sorry left

Closed one of one holes:
`AlgebraicGeometry.Scheme.Modules.exists_isAmple_on_affineOpens_comp`
(node `lem-sfb-quasiprojective-qc-composition`). Zero holes remain in the item;
zero holes were added or split off. This is a complete assembly proof from the
existing dependency declarations; it does not claim to discharge their remaining
proof obligations. The single-file compiler check passed within the 60-second limit.

## No longer needed

Removed the redundant direct private imports of
`Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`,
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`, and
`WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`.
Their required interfaces are already publicly exposed by the three proof dependencies.
No DAG dependency, module or declaration is withdrawn: all three declared assembly
inputs remain needed. The relative-to-absolute ampleness theorem and finite-type
permanence are used through the existing finite-cover theorem, without extra direct
imports here.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or statement repair was needed. The old module docstring
expands the earlier five-step argument, while the current DAG packages its local
work into the two existing dependencies used here. A finite sum of nonnegative
bounds supplies the same common-bound property as the planned maximum, including
the empty-cover case.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
