## What changed

Proved `canonicalIntegralPullbackTensor_associative_spec` and
`canonicalIntegralPullbackTensor_braiding_spec` in
`Sheaf.Paper.DerivedPullbackTensorIso`. Private adjunction cancellation proves the
reduction square for the actual canonical comparison. Private faithful transport
lemmas then reduce its associativity and signed braiding to the stated system
coherence equations.

Added a private reduction functor with an explicit coefficient-sequence target,
and used its full faithfulness in the existing integral constraint proofs.
A generic localization-map HEq lemma replaces concrete substitutions in the two
existing rational coherence proofs. These proof interfaces avoid expensive
category conversions. Public signatures, definition data and public imports are
unchanged. The node records the integral faithful-reduction argument.

Validation: the complete edited module compiled as
`scratchpad/CoherentGenericRationalMap.lean` in 57.9 seconds, exit 0. The delivery tool performs the item-path compilation and consumer checks.

## Proved and sorry left

Closed two of the original eleven holes:

- `canonicalIntegralPullbackTensor_associative_spec`
- `canonicalIntegralPullbackTensor_braiding_spec`

Nine explicit `sorry` bodies remain, all attached to
`lem-pur-derived-pullback-tensor-iso`:

- `pullbackTensorCommonComposition_existsUnique`
- `pullbackTensorCommonAssociator_existsUnique`
- `pullbackTensorCommonBraiding_existsUnique`
- `pullbackTensorRationalScalarUnit_existsUnique`
- `pullbackTensorCommonLeftUnitor_existsUnique`
- `pullbackTensorCommonRightUnitor_existsUnique`
- `canonicalCommonStagePullbackTensor_associative_spec`
- `canonicalCommonStagePullbackTensor_braiding_spec`
- `derivedPullbackTensorIso`

No holes were added or split off. Every added private helper is proved.

## No longer needed

None. No imports, modules or nodes were pruned. The remaining parts of this item
still need the recorded dependencies. The two completed proofs use the existing
system comparison equations and full faithfulness of integral system reduction.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. Profiling showed expensive
conversion between the finite-system and coefficient-sequence presentations,
and repeated concrete-category substitutions in the rational coherence proofs.
Explicitly typed private interfaces and an abstract localization-map helper
avoid those conversions without changing any public statement or construction.

A temporary compile-host filesystem failure (exit 125 before Lean started)
cleared on retry; it is not an outstanding blocker.

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
