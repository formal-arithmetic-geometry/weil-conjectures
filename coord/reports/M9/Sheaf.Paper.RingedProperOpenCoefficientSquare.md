## What changed

Proved the assembly of `SheafOfModules.RingedProperOpen.ringedProperOpenCoefficientSquare`
from the existing normalized ringed calculus and open comparisons, the existing proper/open
clopen geometry, and one new pre-mate compatibility statement. All existing declaration
signatures are preserved. The existing `Factorization` and `t` declarations move unchanged to the new
pre-mate module so that the lemma and its consumer name exactly the same map. The `gamma`, `left` and `right` constructions are
factored through generic constructors
with their exact former unit/map/counit and scalar composite formulas.

The proof constructs the scheme fibre product over the ambient scheme and verifies its
universal property in `Over T`. A generic lemma identifies the actual `gamma` formula
with the adjunction transpose of `t` followed by the left proper counit. A proved private categorical calculation
uses `refinement_coefficient_mate`, naturality and `mateEquiv_counit` to pass from the scalar
compatibility of `t` to the coefficient square for `gamma`. No coefficient or proper mate
is assumed invertible.

Added `Sheaf.Paper.RingedProperOpenPullbackCoefficients`, containing the actual clopen
pullback construction and its scalar compatibility, and updated the parent DAG proof to match.
The existing normalized-operation existence statements are reused directly; their unproved
bodies are existing dependencies, not new holes in this delivery.

## Proved and sorry left

Closed the one original hole in
`SheafOfModules.RingedProperOpen.ringedProperOpenCoefficientSquare`
(node `lem-pur-ringed-proper-open-coefficient-square`) by a complete Lean reduction.

Added one hole:
`SheafOfModules.RingedProperOpen.clopenPullback_coefficients`
(node `lem-pur-ringed-proper-open-pullback-coefficients`). This is exactly the pre-mate
restriction/balancing calculation of original Steps 1--3. Its statement contains no
proper direct image, no `gamma`, and no final coefficient-mate square. The proof combining
this step with the proper adjunctions is complete in the item. This is a decomposition,
with one hole closed and one added, not a net hole reduction. No holes remain in the item.

## No longer needed

Removed these proof imports from the item:

- `Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing`;
- `Mathlib.CategoryTheory.Localization.Pi`;
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`;
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`;
- `Sheaf.Paper.KFlatRingedToposPullback`;
- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`;
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.

The old `lem-cbc-extension-zero-composition` is an etale constant-ring coherence
statement and is not needed for the adjunction-defined ringed open compositor here.
The clopen gluing, localization, K-flat resolution/preservation and cochain balancing
nodes remain mathematical dependencies of the new pre-mate statement. They have not been
pruned from the argument. `lem-sf-open-tensor-normalization` remains in that statement's
proof and in the reused normalized-operation existence theorem. No module is withdrawn.
Obsolete top-level parent `tool_uses` approvals are removed:
`lem-cbc-strict-tower-proper-open-calculus`, `lem-pur-clopen-ringed-module-gluing`,
`lem-weil-pbc-localization-universal-property`, `lem-sfb-product-localization`,
`lem-cbc-extension-zero-composition`, `lem-sf-open-tensor-normalization`,
`lem-pc-kflat-resolution`, `lem-weil-pbc-ringed-pullback-preserves-kflat`,
`lem-pur-cochain-pullback-tensor-coherence`,
`lem-weil-pbc-site-derived-tensor-descent`, and
`lem-weil-pbc-adjunct-counit-identity`. The geometric and pre-mate dependencies
are now recorded at the actual steps that use them; the formal calculation uses
the existing proved mate helper and Mathlib mate counit identity.
The parent uses `lem-cbc-proper-open-clopen-projector` directly for its geometric clause;
it does not invoke `normalizedProperOpenCalculus` or its composition and finite-evaluation
clauses. Existing public imports are preserved as part of the item's exported interface.
The new
`RingedProperOpenPullbackCoefficients` import is public to preserve the exported
`Factorization` and `t` declarations moved there.

## Where the brief, the DAG or earlier work was wrong

The general ring-sheaf operation presentations and open comparisons already have existence
statements in `RingedRefinementCore` and `RingedRefinementClopen`. The parent's proof plan
should reuse those instead of constructing the operations again. The original listed
lemmas do not directly state arbitrary-ring-sheaf coefficient compatibility for the
clopen pullback comparison of a general proper/open square; the new statement records
that exact missing step. The existing refinement compatibility is the identity-left
special case, and constant-coefficient tower compatibility has different coefficient data.
No mathematical statement is changed or disputed.

## New nodes

`lem-pur-ringed-proper-open-pullback-coefficients` states scalar compatibility for the
three specified clopen pullback factors, before any proper mate is taken. The source
is original Steps 1--3, with Stacks Tags 08FJ, 0GL1, 06YS, 06YY and 07A4. Its docstring
and DAG give the restriction bijection, the representative balancing calculation and
localization argument. LeanSearch, LeanFinder, Loogle and Mathlib/repository searches found
ordinary scalar APIs and formal mate lemmas, but no identical geometric compatibility
statement. The identity coefficient map reduces to the normalized units; an empty selected
clopen has zero target, and a full selected clopen reduces to open base change. These edge
cases preserve the stated equation. Change record: `coord/changes/ringed-proper-open-mate-formula.md`.
The three bodies are definitionally unchanged after unfolding `properOpenMate`,
`properOpenLeft`, `properOpenRight` and `ScalarComparisons.chi`. Further change records:
`coord/changes/ringed-proper-open-left-formula.md` and
`coord/changes/ringed-proper-open-right-formula.md`. The mate formula is proved at generic
category level before
instantiation. Every geometric functor is supplied explicitly at specialization;
transparency is respected. Factoring the formula into its explicit generic constructor
addresses the measured kernel-checking stalls. The moved `t` declaration is shared directly. Its pre-mate equation is recorded in the
single-field proposition `PullbackCompatibility`, which prevents repeated expansion of
derived-functor expressions when the generic calculation is specialized. The complete
two-file diagnostic build passed in 43.3 and 54.0 seconds respectively. Profiling, tracing
and temporary heartbeat settings were then removed. The clean two-file compile in
deliver3 passed; the subsequent preflight initially found only two definition-node
signature records containing extra bodies, which were corrected before resubmission.

`def-pur-ringed-proper-open-mate-formula` records the real generic unit/map/counit
constructor used by `gamma` and the two generic scalar-square formulas used by
`left` and `right`. It has no chosen data or proof hole. Its purpose is
to avoid the measured kernel expansion of a specialized mate formula. The sole
consumer is the item itself, held by M9; no external adaptation is required.

`def-pur-ringed-proper-open-pullback-formula` records the actual beta/projector/compositor
word in `t`, its `Factorization` geometry and the single-field `PullbackCompatibility`
proposition. The existing declarations move verbatim to the new pre-mate module; the new
proposition simply names the pre-mate equation. No data is chosen and no hole is introduced.
Change record: `coord/changes/ringed-proper-open-pullback-formula.md`.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
