## What changed

Replaced the sole sorry in `Sheaf.Paper.AdicPerfectModelsCompleteness` by a complete
Lean proof combining the existing completed-model calculation with two separate
presentation/locality comparisons. The theorem signature and all definitions stay
unchanged. The item privately imports `SfbPerfectModelCompletionTransport` and
`SfbAdicCompleteStratumGluing`; both are new modules under `Sheaf.Paper`.

The proof unpacks the original stratified-perfect witness, keeps its covers and
model complexes, derives degreewise vanishing from the strict bounds, applies
`adicPerfectModel_complete_reduction`, extracts `HasCompleteResidueCalculation.1`,
transports this to the Sfb model presentation, and glues using the supplied local
isomorphisms. No new data construction or definition contains a hole. No existing
statement, public import, definition, source-library file, or target was changed.
The existing node now records precisely that combination.

All three modules compiled together through lcompile (11.8 s, 6.5 s, and 16.4 s
respectively, with no errors or warnings). The required delivery checks provide the
final validation after the documentation and DAG update.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.adicPerfectModels_completeness`
(`lem-sfb-adic-perfect-models-completeness`): 1 of 1 original holes has a complete
combining proof. There are zero sorry occurrences in the item module.

Added two holes, each exactly one public theorem in its own new module:

- `AlgebraicGeometry.Scheme.sfbPerfectModel_completion_transport`
  (`lem-sfb-perfect-model-completion-transport`): identifies completeness for the
  two presentations of the same termwise completed coefficient complex. It does
  not assert that either presentation is complete and assumes no perfectness.
- `AlgebraicGeometry.Scheme.sfbAdicComplete_of_stratum_local_iso`
  (`lem-sfb-adic-complete-stratum-gluing`): detects completeness from stratum-local
  isomorphisms to already complete global comparison objects. It does not supply
  complete coefficient models and has no perfectness or model hypothesis.

This is a decomposition, not an axiom-free proof of the mathematical result:
1 original hole closed, 2 strict intermediate holes added, net -1 by hole count.
The two new statements are independent parts of the original argument, not the
original stratified-perfect implication under another name. Their docstrings and
nodes give complete proofs in words, sources, and the existing interfaces to use.

Edge cases checked in the mathematical statements: empty scheme or empty strata;
I=0; I=A; unbounded coefficient complex for the presentation comparison; comparison
objects varying with the covering arrow; and covers with all further pullbacks.
The existing restriction theorem gives ordinary immersion/slice pullback here,
because the completed coefficient map is invertible and the module inverse image
is exact and preserves countable products. No unjustified preservation under an
arbitrary scheme morphism is asserted.

## No longer needed

No existing import was removed and no module or node is globally pruned.
`lem-sfb-adic-perfect-model-complete-reduction` remains a direct mathematical input.
`lem-sfb-adic-stratum-completion-unit` remains needed by the new gluing node, so it
must not be pruned even though the item's complete combining proof does not import
its module directly. The unit's route remains intact.

The combining proof uses only the completeness conjunct of the existing model
calculation. Its residue-comparison and finite-cohomology conclusions are not needed
for this item, but they have other users and are not removed. The separate
perfectness proof in each witness is unnecessary once strict bounds and termwise
finite projectivity are supplied; its declaration and the target hypothesis stay.

## Where the brief, the DAG or earlier work was wrong

The original plan correctly describes the mathematical route, but its existing
Lean dependency signatures do not directly compose. The completed-model calculation
uses the normalized small-site ring and constant-module functor. The item uses the
transported actual completed ring and `CompletedConstantReduction.constantComplex`.
Likewise `adicStratumCompletionUnit_detection` uses `stratumSlicePull`, whereas the
original local-model witness uses `sfbLocalRestriction` and original-site sieves.
Neither existing theorem states the needed comparisons between these presentations.
The new statements isolate exactly those gaps; no source error or false statement
was found. No forced adaptation or change record is needed.

## New nodes

`lem-sfb-perfect-model-completion-transport` is realized by
`Sheaf.Paper.SfbPerfectModelCompletionTransport`. It concerns presentation invariance
alone; completeness of finite-projective models is still obtained from the existing
model calculation. Its proof compares quotient diagrams and their projections,
constant-module realization and scalar extension, and local derived-Hom tests.
The private `constantsIso`, `completionIso`, and `completionIso_projection` in
`CompletedConstantAlgebraFlatQuotients` already implement the coefficient part and
may be reused via a private proof import. That file's Noetherian flatness theorem
is not a hypothesis of the new comparison.

`lem-sfb-adic-complete-stratum-gluing` is realized by
`Sheaf.Paper.SfbAdicCompleteStratumGluing`. Its proof compares the actual restriction
with `SfbAdicRestriction.stratumSlicePull`, then uses both preservation and detection
in `AdicStratumCompletionUnit`. The existing
`Stratification.toFiniteLocallyClosed` in `ConstantModelStratificationTransport`
retains the required domains and immersions; alternatively its record can be built
directly. Generic `lem-weil-pbc-restriction-local-completeness` is used as a tool for
coefficient-isomorphism transport on the fixed small site in both new nodes; no
integral-model unit lemma supplies that generic ringed-site transport. Its public
Lean statement was checked before citing it.

The imported blueprint was searched for derived completeness and strata. There is
no exact duplicate of these interface comparisons. Both nodes remain under
`sk-lem-integral-models`, descended from the completeness sentence of
`det-lem-integral-models-stacks`. There are no change records.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
