## What changed

Proved `beta_comp` from a separate coherence statement for the canonical inverse-image
square, imported privately from `StrictTowerPullbackSquarePasting`. The private,
fully proved `transposed_pasting` lemma computes pasting under arbitrary adjunctions;
`betaInv_unit` verifies that the specified inverse beta maps have these transposes.
The final cancellation recovers the forward beta equation. Both modules compile.

## Proved and sorry left

This is a decomposition: closed the original hole `beta_comp` and added one hole,
`squareG_pasting_inv` (node `lem-cbc-strict-tower-pullback-square-pasting`). The new
statement involves only inverse-image composition; it has neither open extensions
nor proper/open comparisons, and requires no cartesian square.

The six original holes retained, all attached to
`lem-cbc-strict-tower-proper-open-calculus`, are `alpha_cartesian`, `beta_open_comp`,
`alpha_vertical`, `alpha_horizontal`, `alpha_baseChange`, and `gamma_evaluation`.
There are seven holes in the two delivered modules together. `gamma_isIso` already
had a proof and is unchanged.

## No longer needed

None. No existing import or dependency was removed, and the blueprint unit route
is preserved. Only the new inverse-image coherence module is imported for the proof.

## Where the brief, the DAG or earlier work was wrong

The parent plan is mathematically consistent. Its phrase “the same iterated
inverse-image compositor” needs a separate coherence calculation for the specific
section-normalized module, tower and derived compositors; generic adjunction
naturality alone does not discharge that step.

## New nodes

`lem-cbc-strict-tower-pullback-square-pasting` records exactly this geometric
inverse-image coherence calculation. Searches found the constituent Mathlib
`Adjunction.leftAdjointCompIso_assoc` and `SheafOfModules.pullback_assoc` results,
but no declaration for the actual normalized strict-tower `squareG` maps. Its
proof in words describes the sectionwise associativity, conjugation, tower and
localization transport still to formalize. Edge cases include empty schemes,
identity maps and the zero coefficient ring; the construction and statement are
valid in each case.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
