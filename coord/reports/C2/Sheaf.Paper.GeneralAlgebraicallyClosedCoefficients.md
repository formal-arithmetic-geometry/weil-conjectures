## What changed

Retained and checked the earlier proofs in
`Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` against the current build.
Proof irrelevance erases the characteristic parameter. The stage system is
constructed from the published transitions, associators and cocycle, with
uniqueness by dependent function extensionality. Transition additivity uses the
published intrinsic instance; stage additivity follows by equality transport.
Representative transport preserves zero and addition by functor additivity and
bilinearity. The representative criterion uses the upstream pair quotient
calculus. The distinguished criterion exposes the existing Verdier specification.
Specialization identifies transitions and complete stage systems and is exact
by the distinguished-triangle equivalence. Existing signatures, definitions,
visibility, imports and docstrings are preserved.

## Proved and sorry left

Closed 11 of 32 original holes, with no holes added and no split-offs. The closed
declarations are:

- `scalarExtension_parameter_independent`
- `transitionAdditive`
- `associator_existsUnique`
- `stageSystem_existsUnique`
- `stageTransition_additive`
- `transport_additive`
- `representatives`
- `distinguished_iff`
- `specialization_transition`
- `specialization_stageSystem`
- `specialization_exact`

The remaining original holes are:

- `integralScalarCommShift_existsUnique`
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

All names are in `WeilConjectures.GeneralAlgebraicallyClosedCoefficients`.
Every remaining declaration belongs to node
`def-weil-algebraically-closed-coefficients` and retains its existing source
citation and complete natural-language proof plan.

## No longer needed

None. No imports, dependency nodes, or modules were pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or DAG repair was needed. The old `compile.log`
recorded an earlier failed experiment, not the final sandbox. The resumed dry
run of the retained sandbox compiled and passed preflight (AUTO). A direct
additivity proof also compiled but triggered an unused-section-variable warning;
the retained proof preserves the original section-variable dependency and avoids
that warning.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
