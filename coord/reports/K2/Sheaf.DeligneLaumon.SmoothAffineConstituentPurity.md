## What changed

Replaced the whole proof hole of
`AlgebraicGeometry.WeilSheaf.IsReal.exists_isPunctuallyPureOfWeight_cokernel_of_smooth_affine`
with the anchored weight argument in Lean. The original signature and public import
are unchanged. Added one proof import,
`Sheaf.DeligneLaumon.PairEigenvalueCurveTest`, with a single geometric statement.

The proof finds a nonzero closed stalk using the proved source theorem
`exists_nontrivial_stalk_of_not_isZero`, chooses an eigenvalue by
`Module.End.exists_eigenvalue`, and fixes its normalized logarithmic weight.
For each other eigenvalue, the new geometric statement supplies a real ambient
sheaf and an irreducible constituent on one smooth connected curve, together
with the two powered eigenvalues and matching residue cardinalities. The existing
proved curve theorem gives one weight there. A proved private logarithm calculation
cancels both positive powers; nonvanishing of Frobenius eigenvalues and residue
cardinalities greater than one turn the resulting equality into punctual purity.
The proof does not choose data inside a definition from an unproved existence theorem.

The remaining statement has no purity or weight conclusion, and has no selected
embedding or reality assumption. It constructs a curve diagram and tests two
specific eigenvalues. The established curve purity theorem and the complete
anchor calculation are additional, indispensable steps in the parent proof.
This is a decomposition, not a completed proof of the geometric construction.

Validation: the new module compiled through lcompile, and the corrected parent
compiled cleanly through lcompile (exit 0, no warnings). Both Lean files have
lines of at most 100 characters. An overlay DAG traversal found no dependency
path from the new lemma back to its parent.

## Proved and sorry left

Original item: 1 hole. Item after this delivery: 0 holes.

Closed by decomposition:
`AlgebraicGeometry.WeilSheaf.IsReal.exists_isPunctuallyPureOfWeight_cokernel_of_smooth_affine`
(node `lem-zl-smooth-affine-constituent-purity`).

Added and remaining: 1 hole,
`AlgebraicGeometry.WeilSheaf.exists_pair_eigenvalue_curve_test`
(node `lem-zl-pair-eigenvalue-curve-test`), the whole proof of its public theorem
in `Sheaf.DeligneLaumon.PairEigenvalueCurveTest`.

The private positive-power normalization helper is proved. No other hole is
introduced. Net hole reduction is zero; the arithmetic anchor and purity assembly
are now formalized, while the geometric test remains to prove.

## No longer needed

No existing import removed, no module withdrawn, and no global pruning claimed.
The parent now directly uses only the geometric pair test, the existing source
curve purity theorem and elementary stalk/eigenvalue/logarithm facts.

The original direct dependencies
`lem-zl-classical-weil-filtration-heart-transport`,
`lem-zl-geometric-constituents-any-base`,
`lem-zl-constant-extension-mixed-descent`,
`lem-zl-two-point-curve-constituent-purity`,
`lem-zl-curve-testing-irreducibility`, and
`lem-zl-point-weil-heart-flag`
are no longer direct dependencies of the parent's Lean assembly. They are not
claimed withdrawn: the new geometric lemma retains geometric constituents,
classical diagram transport, curve testing and the dimension-zero point case.
It also records the required constant restriction/local Frobenius comparison.

The full mixedness descent theorem
`lem-zl-constant-extension-mixed-descent` is unnecessary for this local purity
assembly: matching positive residue powers descend purity directly. The separate
anchored purity theorem `lem-zl-two-point-curve-constituent-purity` is replaced
here by the explicit Lean anchor computation in the source category. Its
geometric construction remains in the new lemma, with the geometric curve and
local-spectrum dependencies explicitly recorded. The unit's geometric-constituent,
curve-purity, point and descent arguments are retained.

## Where the brief, the DAG or earlier work was wrong

At session start the shared checkout lacked the assigned Lean source even though
its DAG node, queue and landing log existed. There was no rework/quarantine row.
I read the actual landed source from the project server and restored it only
inside this sandbox. Its theorem signature is preserved verbatim.

The existing raw/common-stage comparison theorems do not directly accept source
`AlgebraicGeometry.WeilSheaf` objects. In particular the original filtration
transport, two-point theorem and point-flag declarations concern
`sfCommonStageWeilSheaf`. They cannot be applied by identifying these categories
without a comparison. The new lemma states explicitly the source-category
geometric obligation still missing. Its proof sketch indicates where the
classical/realized diagrams and normalized local Frobenius comparisons must
be implemented; it does not silently assume a category equivalence in the
parent's Lean proof. The proved curve-testing theorem is located in RealSheaves,
which imports this item. To avoid that import cycle, the new node records its
independent finite-etale detector and finite-cover Bertini inputs, with the
dimension-one identity-curve case, rather than requiring an import of RealSheaves.

Edge cases checked: empty X cannot have an irreducible nonzero quotient; zero
stalks impose no eigenvalue condition; a simple quotient is supported on one
clopen connected component, so the two selected eigenvalues are on that
component. The two points may coincide. In dimension zero the supporting
component is a finite-field point, and a constant diagram on its affine line
supplies a curve test. Distinct eigenvalues whose powers coincide are allowed.
Nonsplit extensions in the ambient sheaf are allowed: the argument only uses
its actual subquotient and exact restriction, never its semisimplicity.

## New nodes

`lem-zl-pair-eigenvalue-curve-test` is the geometric diagram and two-eigenvalue
part of the smooth affine argument, in the same chapter and unit. It has one
new module with one whole-proof sorry and a detailed source-based proof in words.
Logged LeanSearch, LeanFinder and Mathlib grep searches found no corresponding
curve-test theorem; whole-blueprint searches found the existing geometric
irreducibility test, which is a dependency, not this powered-eigenvalue statement.
No declaration signature, definition or target statement changes, so no change
record or consumer adaptation is required.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
