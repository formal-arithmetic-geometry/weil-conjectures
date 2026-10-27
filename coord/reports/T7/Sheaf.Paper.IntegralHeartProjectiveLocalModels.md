## What changed

Replaced the proof of `AlgebraicGeometry.ProEtale.integralHeart_projective_local_models`
without changing its statement or its public imports. The proof establishes the canonical
small lifted valuation ring's complete local DVR structure, transports boundedness and
constructible cohomology through an exact equivalence, applies the existing complete-DVR
bounded devissage and stratified-perfect theorem, and constructs small pro-etale covers
from their covering sieves. The pro-etale precoverage's existing Small instance supplies an index restriction that
remains covering, retaining the selected schemes and maps. Its proof uses both joint
surjectivity and the quasi-compact cover refinement.

Added `Sheaf.Paper.IntegralHeartCompletedComparison`, containing the coefficient and
scalar-realization comparison used by that argument, and its node. Updated the item's
proof, proof_deps and proof_origin to describe the actual argument. All new imports in
the item are private proof imports. No existing definition or theorem statement changes,
no source-library file changes, and no consumer adaptations are required.

Validation: lcompile.py --all compiled both delivered modules cleanly, with no warnings:
30.8 seconds for IntegralHeartCompletedComparison and 43.8 seconds for the item.
The item signature is byte-identical to the original signature, and the new node's
lean.statement matches its declaration verbatim. Both changed DAG nodes have acyclic
dependencies; every referenced node exists. Every retained proof import supplies a
constructor, theorem, or instance actually used by the proof.

## Proved and sorry left

Closed the item's one hole, `AlgebraicGeometry.ProEtale.integralHeart_projective_local_models`
(node `lem-sfb-integral-heart-projective-local-models`), by a complete reduction to existing
declarations and one new comparison statement.

Added one hole: `AlgebraicGeometry.ProEtale.integralHeart_completed_comparison`
(node `lem-sfb-integral-heart-completed-comparison`). It states an equivalence of the ordinary
coefficient presentations, its finite-constant constructibility comparison, and its
compatibility with restriction and realization of arbitrary scalar complexes. It does not
assert the existence of any local projective model, bounds, finite generation, projectivity,
a stratification for a derived object, or derived completeness of that object. Thus this is
a strict coefficient-comparison step, not the original local-model existence assertion
under another name. Its full construction and proof are recorded in the docstring and node.

This is a decomposition: one hole closed and one hole added, net zero. The item module
contains zero sorries and the new comparison module contains one. The private domain,
arithmetic and complete-DVR devissage helpers are proved without new holes. The witnesses
of the new existential theorem are eliminated inside the proof of the proposition; no
definition chooses data from an unproved existence theorem.

## No longer needed

No pre-existing import is removed, and no library module is withdrawn or claimed pruned.
The item's original direct proof dependencies on the profinite integer tower, section-action
equivalence and Cartesian coefficients are now used within the lower coefficient comparison,
so they remain needed there. The original DVR theorem, integral cohomological criterion and
adic stratified-perfect theorem remain used. Added the already proved adic-completeness
arithmetic dependency `lem-pod-adic-limit-finite-modules` explicitly.

## Where the brief, the DAG or earlier work was wrong

The public `integral_cohomological_adic_criterion` specializes the field universe to the
scheme universe. The item instead uses the canonical small presentation of an extension in
an independent universe. Its existing proof contains the required general complete-DVR
argument: `perfect_of_completedStratified`, bounded devissage, and the structural assertions
of `adic_stratified_perfect`. The delivery uses those declarations and repeats only their
short combination for the canonical small lifted scalar ring; it does not change the
criterion or coerce unrelated coefficient rings to definitional equality.

The DAG's coefficient and slice identifications were not directly available for the exact
`integralHeartRealization` and canonical-small scalar conventions. Existing
`IntegralConstantModel.constructible_iff` and `smallIntegralCoefficientIso` cover related
fixed-universe and lattice presentations, but do not supply the required arbitrary-complex
local realization comparison for this API. That missing comparison is stated explicitly.

## New nodes

`lem-sfb-integral-heart-completed-comparison` in
`dag/nodes/sec-six-functors-basics/lem-sfb-integral-heart-completed-comparison.json`
realizes the coefficient/slice comparison part of clause (1) of the current integral-heart
local-model blueprint. Its module is `Sheaf.Paper.IntegralHeartCompletedComparison`.
The source, complete proof in words, statement dependencies, proof dependencies, recorded
Mathlib searches, and unchanged unit ancestor are included. Edge cases checked in the
mathematical argument: the empty scheme and strata, zero scalar modules, torsion modules,
and unbounded complexes; no finiteness hypothesis on the scalar complex is needed by a
coefficient equivalence and its natural realization comparison. No change record is needed
because no existing statement or definition was changed.

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
