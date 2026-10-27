## What changed

Reduced rationalPurityTransitivitySummands to the finite-stage normalized purity
adjunction and exact descent of the specified coherent twisted-pullback family.
The exceptional right adjoint is represented by twisted pullback itself through
that adjunction. Gamma and its descent are identities in these counit-compatible
coordinates. The Lean assembly proves the coefficient square, both transitivity
equations, all representative/component clauses of descent, and the finite/Qbar
Karoubi and actual-retract assertions. Its transitivity uses the existing
StageSystem coherence equation; its descent formulas use the published StageSystem
lemmas, and its retract calculation uses naturality, functoriality and i ≫ r = 1.

Moved the already proved declarations through pbcPurityStageC verbatim to the new module
Sheaf.Paper.RationalPurityScalarModels, publicly re-exported by the item. This
makes the actual scalar constructions available to the two new obligation modules
without a circular import. Signatures, data bodies, theorem proofs and visibility
are unchanged. The item also marks the imported scalar comparisons and stage functors locally
irreducible before its first statement, so elaboration does not expand their
full tensor/fraction constructions. This is local to the proof file and changes
no exported reducibility attribute or definition body. The new statement modules
use the original file's local category-instance priorities for the same reason.
The formal descent, identity-comparison, Karoubi and retract calculations are
proved private lemmas over arbitrary categories or StageSystem morphisms. The
pair-category functor, stage inclusion, Karoubi extension and pair-category structure
are locally irreducible during proofs,
after the original definitions. Their published object equations justify the
component formula. RationalPurityPresentationData contains the unchanged
presentation predicates and original coherence obligation. The proved
RationalPurityIdentityDescent specialization separates the concrete descent
calculation from the geometric-bound terms of the final theorem. These are
proved helpers and verbatim moves, not new obligations.
No other existing Lean file changes. The read-only downstream query
and direct-import search both report zero direct Lean importers.

Validation: the final clean lcompile.py --all run compiled all six modules with
exit code 0 under the unchanged per-file limit. Profiling and temporary diagnostic
settings are removed. Static checks confirm unchanged final-theorem and predicate
signatures/bodies, exactly three named theorem holes, valid node JSON and no DAG
cycle through the delivery's nodes.

Change record: coord/changes/A2-rational-purity-scalar-model-relocation.md.

## Proved and sorry left

Original module: 2 holes. Closed its final hole
AlgebraicGeometry.Scheme.rationalPurityTransitivitySummands by a complete Lean
assembly from named intermediate statements. This is a decomposition, not a
sorry-free proof: 1 original hole closed and 2 lower holes added.

The original hole AlgebraicGeometry.Scheme.pbcPurityStageA_coherence remains
unchanged in RationalPurityPresentationData, attached to
def-pur-rational-purity-presentation-data. Only its module and attachment move;
this is the same original hole, not a third added obligation.

Added exactly these two lower holes:

- AlgebraicGeometry.Scheme.pbcPurityFiniteAdjunction in
  Sheaf.Paper.RationalPurityFiniteAdjunction, node
  lem-pur-pbc-finite-purity-adjunction: only the finite-stage adjunction and its
  fixed coefficient counit-mate square. It makes no associator, descent or
  summand assertion.
- AlgebraicGeometry.Scheme.pbcPurityTwisted_exactDescent in
  Sheaf.Paper.RationalPurityTwistedExact, node
  lem-pur-pbc-twisted-exact-descent: only additive/triangulated exactness of the
  induced functor, conditional on the existing coherence obligation. It makes
  no adjunction, purity-square or summand assertion.

Thus the delivery has 3 holes across its 6 Lean modules, one of which is the
unchanged original coherence hole. The relocated scalar-model module has zero
holes. No data is chosen in a definition from either new existence theorem;
their conclusions are eliminated only inside the final proposition's proof.

## No longer needed

No existing declaration, module or unit route is withdrawn. No global module
pruning is claimed. The original public imports remain publicly visible through
the presentation-data and scalar-model APIs. The scalar-model module imports
PbcScalarExtension for its statements;
it has no unused descent or Karoubi import. Its private proof imports still prove
the relocated API, so those dependencies remain needed.

The final assembly does not require finite_stage_karoubian or
pbcIdempotentCompleteTriangulation: its Karoubi assertion follows by functorial
preservation of an identity isomorphism, and its actual-retract assertion assumes
the splitting maps explicitly. Accordingly thm-weil-pbc-finite-stage-karoubian and
thm-weil-pbc-idempotent-complete-triangulation leave the parent's proof_deps.
The unchanged statement dependencies are preserved. The parent also no longer
uses thm-pur-rational-and-qbar-purity as a proof dependency: finite purity is
supplied by the explicit normalized adjunction bridge, proved by the existing
integral-purity route. Other old proof dependencies are retained where used by
the relocated scalar API or the two lower obligations; they are not globally
pruned simply because the parent now cites those modules.

## Where the brief, the DAG or earlier work was wrong

The existing integral-purity and rational-comparison statements concern the
intrinsic coefficient category, not definitionally the lifted PBC categories of
this module. The finite adjunction bridge spells out that remaining comparison
rather than treating the presentations as definitionally identical. Its proof
uses the same simultaneous integral-purity, coefficient-model, and localization
route as the original plan.

The final conclusion existentially specifies an exceptional family by its
adjunction to actual compact support and its counit-mate normalization. It allows
the standard twisted-pullback presentation of that right adjoint. Representing
it this way is why gamma is an identity; this does not drop the substantive
normalized purity-adjunction obligation, which is now precisely the first new
lemma. The main statement, its geometric hypotheses, all existing definitions,
and the unit realization record stay unchanged.

The current blueprint has reorganized the historical parent into rational
adjunction and coefficient-change proofs. Read the latest sk-prop-sp-rational
rational-adjunction proof (1)--(2), sk-thm-purity-transport statement, and its
coefficient-change proof (2)--(3). They explicitly identify twisted pullback as a
right adjoint with the transported counit, and justify this coordinate choice.

## New nodes

- def-pur-rational-purity-scalar-models records the verbatim relocated zero-hole
  API and its existing dependency route.
- def-pur-rational-purity-presentation-data records the original coherence
  obligation, twisted system and five presentation predicates. Every statement
  and definition body is unchanged; the original coherence hole is retained.
- lem-pur-pbc-identity-descent records a proved specialization of the formal
  StageSystem laws, conditional only on exactness. It adds zero holes and keeps
  the component conversion out of the final geometric theorem.
- lem-pur-pbc-finite-purity-adjunction states the finite adjunction and normalized
  counit square. Its docstring gives the complete intended integral-model,
  localized-Hom, and coefficient-normalization proof. Identity/ramified
  extensions, empty schemes and zero inputs obey that same formula.
- lem-pur-pbc-twisted-exact-descent states the independent exactness obligation.
  Its proof proceeds through exact integral operations, rational exact transport,
  shift compatibility of the specified beta, and pbcDescentFunctors. The even
  shift [2d] accounts for the shift sign; d = 0 and zero/empty cases are included.

The parent node's proof, proof_deps, proof_origin and Lean attachment follow the
actual assembly. The relocated declarations attach to the new API node; all
original public names remain available through the item. Searches are recorded
from this session's msearch log, and blueprint searches found no exact duplicate
for the lifted PBC statements.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
