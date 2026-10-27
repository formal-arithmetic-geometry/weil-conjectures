## What changed

Only Sheaf.Paper.FiniteCompactSupportEvaluationRefinement and its existing DAG node change.
The etale proper/open comparison specializes singleLevelFiniteProperOpenTransport with
identity scalars. Its isomorphism consequence transports through the retained etale
antecedent and proves ordinaryC_isIso. pullOrigin retains the actual pulled-back complex,
antecedent, and canonical site and coefficient-presentation comparisons.

Cofilteredness equalizes parallel refinement
arrows; ordinaryC composition and isomorphism cancellation then give ratio independence
and the cocycle. Two refinement/exchange equations imply ordinaryI_exchange.
transport_pasting is the original pasting equality after cancelling the middle inverse pair.
Derived adjunction evaluation reuses evaluation_units_counits verbatim. evaluationF_isIso
uses evalR_isIso and evalJ. presentation_isIso uses the equivalence of finite scalar
presentations and the existing theorem that mates along equivalences are invertible.

Some existing declarations move earlier within the same file to make these proofs
available at their point of use. Their signatures, bodies and visibility stay unchanged.
Private proved helpers implement the normalization and cancellation calculations.
Large derived-operation definitions are locally kept irreducible during elaboration.
The existing node records the additional already-stated proof dependencies.

## Proved and sorry left

Original holes: 14. Holes closed: 9. Holes added: 0. No split-off statements.
All names below are in AlgebraicGeometry.ProEtale.StrictTower.FiniteCompactSupport.

Closed: ordinaryGamma_etale; ordinaryC_isIso;
pullOrigin; ordinaryI_independence_cocycle;
ordinaryI_exchange; transport_pasting; derived_adjunction_evaluation; evaluationF_isIso;
presentation_isIso.

Remaining, each attached to lem-pur-finite-compact-support-evaluation-refinement:
finiteCompactSupportEvaluationRefinement; refinement_evaluation;
ordinaryC_identity_composition; ordinaryC_exchange;
ordinaryE_specified.
These are the original statements with their original source and proof docstrings.
The ratio independence and cocycle proofs depend on the remaining
ordinaryC_identity_composition; ordinaryI_exchange depends on ordinaryC_exchange.
The etale transport proof depends on the already stated single-level finite proper/open
transport theorem. This is a partial proof of the original module, not a claim that its
entire axiom closure is sorry-free.

## No longer needed

Removed unused private proof imports: WeilConjectures.Compactification.CategoryBaseChange, Sheaf.AlgebraicGeometry.FiniteClopenMateSiteTransport, Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization, WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange, Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange.
Added the direct proof import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar.
No module or DAG node is withdrawn. The remaining five original obligations retain
their original mathematical proof plans. No unit-level route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The item has 14 original theorem holes (the initial progress update miscounted 15).
The DAG plan is usable, but ordinaryGamma_etale is already exactly the
identity-scalar specialization of SingleLevelFiniteProperOpenTransport. Reusing it
avoids restating or splitting its argument. The attempted direct exchange-evaluation
proof and constant-support transport calculation exceeded the kernel checking limit;
their original named obligations remain intact.
No mathematical statement correction,
changed hypothesis, hollow definition, or forced adaptation is included.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
