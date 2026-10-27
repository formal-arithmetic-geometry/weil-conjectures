## What changed

Reduced `AlgebraicGeometry.ProEtale.BoundaryFiniteSite.boundary_finite_site_realization`
by proving its entire finite-Tor site-comparison step for both schemes. The item theorem
signature and all eleven existing definition signatures remain unchanged. No adopted
source-library file changes.

Added the proved theorem `boundary_finite_tor_comparison` in
`Sheaf.Paper.BoundaryFiniteTorComparison`. It supplies the restricted equivalence for the
actual ordinary comparison functor, preservation and reflection of every ordered Tor
interval, and etale finite-Tor representatives of all pro-etale finite-Tor objects.
Its proof uses the existing finite-ring constructible-origin theorem, exact intrinsic
coefficient realization, fixed-scalar Tor comparison and bounded-below full faithfulness.
Finite cohomology support is converted to an ordered interval, including empty support.
The assembly applies this theorem to T and Z and combines all six results with the
remaining boundary step.

Moved the eleven existing definitions into the publicly re-exported
`Sheaf.Paper.BoundaryFiniteSiteData`, allowing the two step modules to import their
interfaces without a cycle. Nine bodies are verbatim. BasicConclusion explicitly names
its final six clauses BasicRemainder; SiteConclusion explicitly names its canonical
evaluation specialization EvaluationAt. Unfolding these two new definitions restores
the old formulas, including the original counit predicate. This bounds repeated expansion
of large canonical functor expressions. All five old public imports remain available.

The remaining theorem is in `Sheaf.Paper.BoundaryFiniteEvaluationRealization`. It states
BasicRemainder and EvaluationAt under the original etale hypotheses. It omits the six
finite-Tor comparison clauses proved in the first step. Node records follow this route.

## Proved and sorry left

The original module had one hole:
`AlgebraicGeometry.ProEtale.BoundaryFiniteSite.boundary_finite_site_realization`.
Its assembly now has no hole. The new
`AlgebraicGeometry.ProEtale.BoundaryFiniteSite.boundary_finite_tor_comparison`
is completely proved, including all three conclusions, with no hole.

One hole is added and remains:
`AlgebraicGeometry.ProEtale.BoundaryFiniteSite.boundary_finite_evaluation_realization`
(node `lem-weil-boundary-finite-evaluation-realization`). Its proof is exactly `by sorry`,
with its original source and complete natural-language proof in the docstring.
This is a decomposition: one original hole closed and one strictly smaller hole added
(net zero). It is not a claim that the whole boundary-realization mathematics is proved.
No private declaration or definition contains a hole.

## No longer needed

Removed the original private imports from the item/data header:
`Sheaf.CategoryTheory.FullyFaithfulExceptionalHomTransport`,
`Sheaf.Paper.ProEtaleConstructibleOrigin`,
`Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`,
`Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula`,
`Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`,
`Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`, and
`Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`.
The assembly uses only the two new step modules. The larger constructible-origin
package is replaced in the proved finite-Tor step by the direct intrinsic finite-ring
origin result. The counit, projection, monoidal and evaluation ingredients stay as
recorded dependencies of the remaining boundary step, or are encapsulated by its
existing boundary projection-comparison dependency.

The parent now directly depends only on the new finite-Tor comparison and the remaining
boundary step. Its old dependencies are handled as follows:
`lem-exc-comparison-tor-interval` and `thm-weil-pbc-site-comparison` supply the fixed-scalar
Tor and Hom tools for the proved step; `lem-sf-proetale-constructible-origin` is replaced
there by `lem-weil-pbc-finite-ring-constructible-derived-origin`;
`lem-sf-fully-faithful-exceptional-hom-transport`,
`lem-weil-pbc-comparison-direct-image-canonical-mate`, and
`lem-weil-pbc-closed-immersion-proper` are encapsulated by boundary projection comparison;
`lem-weil-boundary-etale-adjunction-restriction`,
`lem-weil-boundary-proetale-projection-comparison`,
`lem-sf-ringed-derived-closed-symmetric-monoidal`,
`lem-weil-boundary-dualizing-composition`,
`lem-weil-boundary-proetale-q-compatibility`,
`lem-weil-finite-compact-projection-formula`,
`lem-weil-finite-duality-site-comparison`, and `lem-weil-pbc-comparison-pullback`
remain in the residual proof plan. Its proper projection isomorphism can use the
stronger existing `lem-etale-proper-projection-formula-finite` directly.
Removed only the obsolete top-level tool_uses entry
`lem-sf-proetale-constructible-origin`; all other approvals retain their order.
No module is withdrawn and no global pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

No false statement was found and no hypothesis or conclusion was weakened. Existing
ordinary fixed-scalar Tor comparison works even without a bounded-below hypothesis,
so the interval step is shorter than the planned coefficient-model route. The finite-ring
constructible-origin theorem gives the exact intrinsic essential image; full faithfulness
of coefficient realization cancels it to obtain fixed-scalar representatives.

Edge cases checked: zero complexes, empty homology support, empty schemes, the identity
immersion and coefficient level one. The finite-support helper uses min/max to give an
ordered interval even when support is empty. The residual keeps every original etale
preservation hypothesis, all canonical arrows, and both invertibility assertions.
The unit's statement and proof route remain unchanged.

An exploratory full dependency audit found a pre-existing cycle between
`lem-pc-ring-hom-extension-differential` and
`lem-pc-ring-hom-extension-differential-adjacent`, reached through existing finite-Tor
definition dependencies. The packet adds no edge to those unrelated nodes. Reported
for the maintainer rather than editing unrelated work.

## New nodes

`def-weil-boundary-finite-site-data` records the eleven relocated definitions and the
explicit BasicRemainder/EvaluationAt factoring. Existing signatures are unchanged;
unfolding the factoring restores the old bodies. No data is chosen from existence.

`lem-weil-boundary-finite-tor-comparison` records the proved restricted equivalence,
interval comparison and etale representatives on one scheme, applied twice by the item.

`lem-weil-boundary-finite-evaluation-realization` records the remaining boundary part,
strictly excluding both restricted equivalences, both interval clauses and both
representative clauses. It retains Hom, geometry, counit/projection and evaluation
compatibility with the complete source argument in its docstring.

Change record: `coord/changes/C8-boundary-finite-site-step-modules.md`.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
