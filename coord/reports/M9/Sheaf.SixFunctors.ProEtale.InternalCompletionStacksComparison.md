## What changed

Replaced the single hole in
`AlgebraicGeometry.ProEtale.internal_completion_stacks_comparison` by a proof from the
existing general `CategoryTheory.ringedKoszulCompletionReflector`, native K-flat resolutions,
`AdicCompletion.isDerivedComplete_iff`, and two strictly smaller comparison steps.
The theorem's signature and its public imports are unchanged.

`InternalCompletionSectionTransport` constructs the prescribed composite of derived
point-coefficient restriction, constant scalar restriction, and small-site section transport.
Its section equivalence, additive instances, derived conservativity, comparison with
`smallDerivedObject`, and invariance of completeness under isomorphism are proved.
The section-equivalence argument is the existing private argument in
`IntegralModelsStacks`, reused without changing that module. The derived conservativity
argument uses homology, so it applies to arbitrary unbounded complexes.

The remaining algebraic calculation is in `InternalConstantResidueGenerator`. The remaining
augmentation-preserving comparison of derived limits on K-flat representatives is in
`InternalQuotientKoszulUnitComparison`. Each has its own module, statement, proof in words,
source, and node. The main proof chooses the generator and a Koszul presentation, compares
units on a K-flat representative, cancels the comparison isomorphism, reflects
invertibility, and transports the local predicate to the exact object in the target. The residue-kernel
inclusion is proved monic by sectionwise subtype cancellation, as in the existing
`FlatRingedIdealCompleteEquivalence` proof.
It introduces no chosen completion data or hollow definition.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.internal_completion_stacks_comparison` (1 of 1).
This is a decomposition, not an unconditional proof: two new holes remain, so the packet's
net progress by the hole count is -1 (1 closed minus 2 added).

- `AlgebraicGeometry.ProEtale.InternalCompletionTransport.residue_generator`, node
  `lem-sfb-internal-constant-residue-generator`: existence of a singleton global generating
  list for the first residue kernel. This has no derived object or completeness predicate.
- `AlgebraicGeometry.ProEtale.InternalCompletionTransport.quotient_koszul_unit_comparison`,
  node `lem-sfb-internal-quotient-koszul-unit-comparison`: comparison of the actual augmented
  quotient Roos object with a prescribed singleton Koszul completion on a K-flat
  representative. It asserts a unit-compatible isomorphism, not either direction of the
  target completeness equivalence.

There are no holes in `InternalCompletionSectionTransport` or the item module.
The supporting API proves `smallModules_equivalence`, `functor_reflects`, `objectIso`, and
`complete_iso`, as well as the additive and equivalence instances.

## No longer needed

No existing module is withdrawn and no public import is removed. No global pruning is
claimed. The original normalized coefficient-limit and constant-coefficient-criterion
nodes remain needed in the proof plan of the quotient/Koszul comparison, rather than as
direct dependencies of the final combination. The unit's route is retained.
The alternative `IntegralModelsCompletionTransport` route was inspected but not imported:
it starts from `IsSfbAdicComplete`, and does not itself identify the actual native Roos
augmentation with that predicate.

## Where the brief, the DAG or earlier work was wrong

The original plan's statement that section and scalar transport identify the two
augmentations is mathematical work: the normalized coefficient limit and flat common
quotients do not state an augmented derived-limit comparison for the native Roos complex.
The delivery makes that exact missing chain-level step explicit. Likewise the generic
Koszul reflector requires a specified local generating list for the actual kernel,
which was implicit in the former plan. Neither an object isomorphism alone nor a
constructible/bounded special case suffices for the target, so the new comparison retains
the unit on arbitrary K-flat representatives.

`RingedKoszulCompletionReflector` supplies the general ringed-site interface directly;
the recorded node `lem-weil-pbc-ringed-koszul-completion-reflector` is also reexported by its
recorded module `Sheaf.Paper.WeilCompletedTensorReflector`. Its existing attachment is not
changed. No existing statement, definition, target, consumer, or source-library declaration
was altered. A source-only closure traversal encountered the pre-existing unrelated
cycle `lem-pc-ring-hom-extension-differential` /
`lem-pc-ring-hom-extension-differential-adjacent`; this packet changes neither node. The local choice of a generator is used only inside the proof, not to define data.
Empty X and zero P satisfy both new statements; singleton generation is
sheaf-local, and no assertion of sectionwise surjectivity on arbitrary sites is used.

## New nodes

`def-sfb-internal-completion-section-transport` records the actual exact conservative
transport and its proved API. Its functor is an explicit composite of existing functors.

`lem-sfb-internal-constant-residue-generator` isolates the underived residue-kernel
generator calculation, the first ingredient needed by the general reflector.

`lem-sfb-internal-quotient-koszul-unit-comparison` isolates the normalized unit-compatible
derived-limit comparison on K-flat complexes. Representative independence, conservativity,
and the local-completeness reflector remain outside this statement and are combined in
the proved item module. This is a proper step of the original argument, not a renamed
completeness equivalence.

No change record is required: only the item's proof and route metadata change, and the
three additional modules introduce new declarations. No existing interface changes.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
