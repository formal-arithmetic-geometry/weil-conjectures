## What changed

`Sheaf.TraceFormula.GradedImmersionAmpleCriterion` now has a complete Lean proof of
`AlgebraicGeometry.Scheme.Modules.graded_immersion_ample_criterion` from the geometric
dependencies and one separate affine-chart comparison. Its statement is unchanged.
The proof constructs the lift to an absolute Proj chart, transports the submodule
grading to additive subgroups, cancels the open chart to obtain an immersion, factors
through a quasi-compact open and a closed immersion, and combines the two twist
results with closed-immersion preservation of ampleness. A proved private helper
obtains ampleness from a positive power directly from the definition.

The structure `RelativeGradedLineMap` and its definitions `evaluate`,
`GeneratesEverywhere`, and `IsCanonicalMap` move verbatim to
`Sheaf.TraceFormula.RelativeGradedLineMap`, publicly re-exported by their original
module. This prevents an import cycle with the new affine-chart theorem. The change
record is `coord/changes/relative-graded-line-map-module-S2.md`. No source-library
file, existing signature, definition body, or target statement changes.

The genuinely separate affine chart result is stated in
`Sheaf.TraceFormula.RelativeGradedMapAffineChart`: its conclusion is the basic-open
and homogeneous-fraction formulas. The item itself now constructs the normalized
graded section map, proves generation over the fixed affine open by degreewise
base-change induction, and proves preservation of nonvanishing under pullback
using the fibre comparison. These parts have complete private proofs.
It has no quasi-compactness or immersion hypotheses and no ampleness conclusion.
The main theorem proves the remaining geometric argument from this result.

Validation: the three delivery modules compile; the integrated item compiles cleanly
in 22.6 seconds. All three original direct consumers
(`ProjectiveBundleRelativeAmple`, `RelativeAmpleVeryAmple`, and
`LineQuotientHomogeneousFractionMap`) and the additional definition consumer
`LineQuotientChartInversePullback` compile unchanged. Temporary validation copies
are not part of the delivery. The DAG proof and definition ownership were updated.
The delivery preflight additionally identified four inferred constant users absent
from the original change-record table. These are now recorded; the unchanged
`LineQuotientTrivializedCoefficients`, `NodalLogCanonicalReconstruction`, and
`ProjectiveBundleQuotientGeometry`, together with the previously tested
`RelativeAmpleVeryAmple`, all compile unchanged in the expanded consumer check. No consumer files are
part of the delivery.

## Proved and sorry left

Closed the original single hole in
`AlgebraicGeometry.Scheme.Modules.graded_immersion_ample_criterion`.
Added one hole, solely in the public theorem
`AlgebraicGeometry.Scheme.Modules.RelativeGradedLineMap.affine_chart_formulas`.
Its proof is exactly `by sorry`, with its source and complete proof in words in
its docstring and its new node. This is a decomposition: one hole closed and one
added, net zero; it is not a claim that the full target closure is now sorry-free.
There are zero holes in either the item module or the extracted definition module,
and zero holes in definitions. The private positive-power helper is fully proved.
The additional private helpers
`boundary_adj_eq`, `boundary_unit_transport`, `evaluate_add`, `evaluate_one`,
`boundary_tensor_unit`, `power_add_hom`, `evaluate_mul`, `exists_graded_map`,
`exists_evaluation_map`, `fixed_affine_generation`, `residue_zero_iff`,
`nonvanishing_pullback_open`, and `evaluation_cover` have no holes. The algebra
construction, fixed-affine generation, and arbitrary-open nonvanishing probes
compiled before integration.
Existing holes in imported modules are not closed or newly introduced here.

The remaining affine-chart proof requires only the frame-wise identification with
`fromOfGlobalSections` and its basic-open and fraction equations. The normalized
graded map, fixed-affine generation, and nonvanishing under pullback are proved in
the item, rather than included in the split-off conclusion. The residual is the
separate canonical-map argument of Stacks 01O9/01NK, rather than a renaming of the immersion criterion.

## No longer needed

Removed the direct proof import of
`WeilConjectures.AlgebraicGeometry.AmplePositiveTensorPower`. The node
`lem-sc-ample-positive-tensor-power` is no longer a proof dependency or tool use:
`exists_common_degree_twist_ample` already says that every positive multiple is
ample. The final descent from a positive power is proved directly in the item.
Removed the unused private import
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.

Removed the public import of `Sheaf.TraceFormula.SpaceLineModuleProjMap` and its
obsolete proof tool use `lem-trf-space-line-module-proj-map`. The criterion receives
`r` and `hr` as hypotheses and uses the specialized affine characterization; it does
not construct the general algebraic-space canonical map or use its unrestricted
base-change theorem. Its original statement dependency is retained, since the
mathematical statement names that construction. This is not a withdrawal of that
node or its module; other consumers can still need it.

Removed redundant direct public imports of `Mathlib.AlgebraicGeometry.Scheme`,
`WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
`WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra`,
`WeilConjectures.AlgebraicGeometry.GradedSheafStructures`,
`WeilConjectures.AlgebraicGeometry.RelativeProj.Basic`, and
`Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`. The definition module
provides these interfaces transitively. No mathematical dependency is pruned merely
by removing a redundant import. No module is withdrawn and no claim is made that
these source declarations become globally unused.

All remaining original geometric proof dependencies are used. In particular the
quasi-compact-open twist theorem, absolute twist comparison, closed-immersion
ampleness theorem, and immersion factorization remain required.

## Where the brief, the DAG or earlier work was wrong

The original Step 1 referred to the general relative-Proj construction as though its
recorded Lean theorem directly supplied the absolute graded section map and fraction
formulas. Its interface is instead an algebraic-space construction with scheme-test
families. The criterion's scheme-only graded map has its own recorded definitions.
The missing basic-open and fraction comparison is therefore stated separately,
without extra geometric hypotheses. The item constructs the graded map and proves
the generation reduction itself, then uses the comparison's precise formulas.

The original route used the multiplication-isomorphism clause and a separate theorem
on positive powers of an ample module. The recorded quasi-compact-open theorem is
stronger: its ampleness clause already applies to every positive multiple. Using
that clause removes the extra step without changing the unit's affine-reduction,
immersion-factorization, twist-comparison, and ampleness argument. No global twist
multiplication isomorphism is asserted for arbitrarily graded rings.

The launcher pause/resume reset the split-off reference clock. The original work
began on 2026-10-23 at 09:50 UTC; interrupted delivery attempt 36840 had no delivery
record or active process on resume. Retry 75210 was refused before pushing at
16:56 UTC because the fresh reference clock showed only five minutes. I retained
the packet and continued substantive proof work: construction of the normalized
graded section map, fixed-affine generation by degreewise base-change induction,
and nonvanishing under pullback of a section over an arbitrary open. No launcher
metadata or scripts were changed. This records the reset and attempt identifiers
for the launcher owner, as required by the current brief.

## New nodes

`lem-trf-relative-graded-map-affine-chart`, a statement in the item's chapter and
unit, attached to
`AlgebraicGeometry.Scheme.Modules.RelativeGradedLineMap.affine_chart_formulas`.
Its source is Stacks Constructions 01O9, characterization (3), and 01NK. It assumes
the normalized graded map and its nonvanishing cover and concludes only the two
canonical chart formulas. Searches
of the current blueprint and DAG found no equivalent statement. Logged LeanSearch,
LeanFinder/Loogle, and Mathlib grep searches found ordinary Proj restriction lemmas,
not this relative line-module comparison. Its node includes those actual searches.
Empty schemes, empty affine charts, arbitrary degree-zero algebras, and generators
in arbitrary positive degrees are covered. Tensor-product elements need only finite
sum presentations; finite generation of a graded piece is not required.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
