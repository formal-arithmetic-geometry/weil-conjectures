## What changed

Reduced `WeilConjectures.ReconstructedPairRefinement.systemDown_isIso` to the
single finite-evaluation theorem in the new module
`Sheaf.Paper.RefinementFiniteOriginEvaluation`. The proof applies the supplied
coefficient calculus's joint conservativity to the actual intrinsic refinement,
transports each etale-origin witness through the quotient-coordinate counit,
and then uses functoriality and invertible outer coordinate/beta comparisons.
Existing declaration signatures, targets and public imports are preserved.
The `systemDown` body is factored through the new public `conjugate` and `conjugateComponent` definitions,
which record exactly its original five-factor component expression and the
original composite's naturality. This avoids expensive
kernel conversion at the specialized categories; no map or comparison changes.
The complete item compiled in 33.7 seconds. The change record is
`coord/changes/reconstructed-pair-refinement-conjugation.md`.

The new statement concerns one chosen positive coefficient level. Unlike the
original theorem it has no global lower-bound hypothesis, no assumptions at other
levels, no pair of Brown compact-support presentations, and no reconstructed map.
Identity refinements, the first positive quotient (Lean index zero), zero inputs,
and unnormalized systems were checked against its mathematical proof.

## Proved and sorry left

One of the two original holes is reduced:
`WeilConjectures.ReconstructedPairRefinement.systemDown_isIso`
(lem-pur-reconstructed-pair-refinement-coherence).

One new hole is split off:
`WeilConjectures.ReconstructedPairRefinement.systemRefinementEvaluation_isIso`
(lem-pur-refinement-finite-origin-evaluation).

The original hole
`WeilConjectures.ReconstructedPairRefinement.reconstructedPairRefinementCoherence`
(lem-pur-reconstructed-pair-refinement-coherence) remains unchanged.
`output_origin` was already proved before this delivery.

This is a decomposition: one hole closed, one added, net zero. There are two
remaining holes across the delivered Lean modules, each a named public theorem.

## No longer needed

Removed the unused proof imports
`Sheaf.AlgebraicGeometry.CompactificationRefinementCoherence`,
`Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting`, and
`WeilConjectures.Compactification.CategoryBaseChange`. They were present before the
delivery, but the implemented proofs do not refer to their declarations. No module
or DAG dependency is withdrawn. The main coherence theorem retains its
existing eight-step proof plan and therefore its planned dependencies. The new
invertibility reduction itself needs only the finite-evaluation lemma, the
supplied joint-conservativity field, and the definitions already publicly imported.
The global lower-bound component of `Site.Origin` is unused in this reduction;
each level's etale witness has its own lower bound.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The original DAG's first step
contained a finite-evaluation calculation not separately exposed in the existing
Lean API. The new node records precisely that part; the joint-conservativity and
coordinate-conjugation argument is implemented in the parent module.

## New nodes

`lem-pur-refinement-finite-origin-evaluation`: the actual intrinsic system refinement
is invertible at one positive finite coefficient level admitting a bounded-below
etale origin in the published quotient coordinates. Source: Stacks 0F7B and the
parent's Step 1; the docstring and node give the finite normalized mate calculation.
It is strictly part of the original argument. The definition refactor is recorded in
`coord/changes/reconstructed-pair-refinement-conjugation.md`.

## Second reading by Z9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
