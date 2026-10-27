## What changed

Replaced the body of `WeilConjectures.IntegralSystemRealization.integralSupportTowerNormalization` by an explicit construction. The prescribed tower and evaluations are extracted unchanged, as is the all-pairs transition equation. The whole-input strict comparison is restricted to the support domain. The open-mate theorem gives the actual invertible reconstruction unit and open reduction map. Their restricted natural transformations give natural isomorphisms; total limit, proper image, and the canonical qcqs realization construct the integral comparison. Its component formula is checked directly. A proved private categorical lemma, `scalarProjection_comp`, transports a normalized finite map through the scalar-adjunction Hom equivalence. Applying it to the canonical realization's existing projection specification gives the final finite identity.

Added two modules for the unresolved normalization calculations:
`Sheaf.SixFunctors.IntegralSupportStrictTowerComparison` treats only the strict tower and its evaluation equation, over an arbitrary field and on every integral input. It has no realization model, integral comparison, reconstruction-unit condition, or constructibility conclusion.
`Sheaf.SixFunctors.IntegralSupportProjectionTransport` treats only the projection equation for the already specified proper/open comparison, for an arbitrary input with invertible actual open-output unit. It has no chosen compact-support tower or constructible compact-support action and asserts no existence of an isomorphism.

Existing signatures, definitions, public imports and the unit route are preserved. Local irreducibility controls keep the fixed calculus and derived-category instances from unfolding during this proof; their definitions are unchanged. Validation: `lcompile.py --all` compiled all three final modules successfully on the project server after removing diagnostics. The profiled assembly itself previously compiled in 10.9 seconds; the clean all-files run also passed. All writes are confined to this item's sandbox.

## Proved and sorry left

The original single hole in `WeilConjectures.IntegralSystemRealization.integralSupportTowerNormalization` (node `lem-sf-integral-support-tower-normalization`) is replaced by a complete proof from named dependencies. This is a decomposition, not an unconditional proof of the geometric normalization. Holes closed: 1; holes added: 2; net holes: +1. The item itself has zero remaining textual holes.

The added holes are:

- `WeilConjectures.IntegralSystemRealization.integralSupportStrictTowerComparison`, node `lem-sf-integral-support-strict-tower-comparison`.
- `WeilConjectures.IntegralSystemRealization.integralSupportProjectionTransport`, node `lem-sf-integral-support-projection-transport`.

No hole occurs inside a definition or a private helper. The existing `integralOpenMateNormalization` dependency is used with its unchanged statement and is not counted as a new hole of this delivery.

## No longer needed

No existing public or proof import is removed. The original item had only its statement import.

The direct proof dependency `lem-sf-integral-reduction-pullback-model` / `Sheaf.SixFunctors.IntegralReductionPullbackModel` is unnecessary: the theorem already receives `model`, so it never constructs a new realization model. It is not imported.

`lem-coef-derived-system-evaluation-calculus` and `lem-sf-compact-support-restriction-of-scalars` are no longer direct steps of this item's assembly. They remain necessary in the new strict-comparison and projection-transport proof plans, so they are not claimed globally pruned. The direct dependency `def-sf-integral-system-operations` is retained for the canonical operations and quasi-compactness cancellation. No module is withdrawn and no upstream declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The listed declarations supply the chosen strict tower with all-pairs transitions and the open reconstruction isomorphisms, but none states the two coordinate-normalization identities needed to combine these interfaces. The new lemmas isolate the exact first-step strict comparison and second-step projection transport. The closest existing `CompactificationCompletedRealization.strictRealization` begins with reduction of the completed geometric image using an existential calculus; it does not compare the specified operations applied to the fixed input reduction. `PurCompactSupport.comparison_projection` concerns the tensor projection formula, not the total-limit coefficient projection. Neither states either new coordinate identity. The original proof plan remains the mathematical route. The main proof does not infer equality of derived arrows from their finite evaluations.

The new statements were checked on zero input, empty and identity open immersions, and the equal-exponent case: they require no nonempty or positive nonzero object assumption. The strict comparison has no extra boundedness or constructibility restriction. The projection calculation assumes the invertibility it explicitly uses; the item obtains it from the existing open-mate theorem. No target or existing statement is weakened.

## New nodes

`lem-sf-integral-support-strict-tower-comparison` records the whole-input strict comparison and evaluated normalization, a proper part of the original theorem's first step. Its module is `lean/Sheaf/SixFunctors/IntegralSupportStrictTowerComparison.lean`.

`lem-sf-integral-support-projection-transport` records the proper/open projection calculation before the integral constructible realization, a proper part of the original theorem's second step. Its module is `lean/Sheaf/SixFunctors/IntegralSupportProjectionTransport.lean`.

Both nodes include their source, complete proofs in words, statement and proof dependencies, library/Mathlib searches, Lean signatures, and the unchanged unit ancestry. No change record is required: existing interfaces are unchanged.

## Second reading by J8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
