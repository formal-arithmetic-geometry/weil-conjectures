## What changed

Proved `integralScalarCommShift_existsUnique` in
`lean/Sheaf/Paper/GeneralAlgebraicallyClosedCoefficients.lean`.
A private general lifting lemma constructs the shift with `Functor.CommShift.ofComp`.
Its component formula follows from the canonical ordinary/completed comparison;
faithfulness and cancellation give uniqueness. Added the private proof import
`Sheaf.Paper.SfIntegralConstructibleTriangulated` for the intrinsic inclusion's
shift structure. Public signatures and non-theorem bodies are preserved.

The complete module compiled in 56.5 seconds before a subsequent compile-server
storage failure. Later exploratory proofs are retained only in the sandbox scratchpad
and are excluded from this delivery.

## Proved and sorry left

Closed 1 of the 21 original holes:
`WeilConjectures.GeneralAlgebraicallyClosedCoefficients.integralScalarCommShift_existsUnique`.
Added no holes and split off no statements.

The following 20 existing holes remain in namespace
`WeilConjectures.GeneralAlgebraicallyClosedCoefficients`, all attached to
`def-weil-algebraically-closed-coefficients`:

- `transitionCommShift_existsUnique`
- `transitionExact`
- `associator_cocycle`
- `stageTransition_exact`
- `transportSystem`
- `homCoordinates_existsUnique`
- `composition_bilinear`
- `inclusion_additive`
- `shift_existsUnique`
- `zero_exists`
- `transitionIso_commShift`
- `commonStage_cone`
- `specialization_comparisons`
- `specialization_transitionShift`
- `specialization_pairs`
- `specialization_transport`
- `specialization_homCoordinates`
- `specialization_additive`
- `specialization_commShift_existsUnique`
- `specialization_distinguished`

## No longer needed

No original import, declaration, node or module is removed. The integral-shift proof
needs no new intermediate admitted statement. Its direct fully faithful lifting
argument uses no auxiliary finite-field datum. The exploratory proof import
`Sheaf.Paper.FiniteFreeCompletedScalarComparison` is unnecessary and excluded.
No dependency used by the remaining open obligations is declared globally obsolete.

## Where the brief, the DAG or earlier work was wrong

The owning node had no proof steps for these concrete obligations. Its updated route
records the completed integral-shift argument and explicitly leaves the others open.
An earlier sandbox report prematurely described all 21 proofs as completed; this
report corrects it. The full exploratory draft has not passed the module compile gate.

The compile server subsequently rejected multiple independent jobs before Lean began:
`stdbuf: failed to create temp directory: No space left on device (os error 28)`.
No launcher or server file was modified to bypass this failure.

## Second reading by P7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
