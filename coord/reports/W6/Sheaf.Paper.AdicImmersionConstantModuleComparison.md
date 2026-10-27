## What changed

Proved `AlgebraicGeometry.Scheme.sfbImmersion_constantModuleComparison` with its original
signature and all definitions unchanged. The proof first reuses the proved ordinary
`completedRealizationIso` in `SfbPerfectModelComplexComparison`, identifies its completed
coefficient isomorphism with `SfbCompletionNormalization.coefficients` by finite projections,
and cancels inverse scalar restrictions.

For the specified algebraic inverse image, the proof constructs the natural constant-module
comparison from the coproduct-of-terminal-objects comparison on underlying sets. The existing
`constantInverseImageScalarNormalization` theorem and the sheafification adjunction identify
transported constant scalars with target constant sections. The proved `constantPullback_scalar`
then gives scalar compatibility. Finite-limit-preserving functors lift the natural set comparison
to additive sheaves, and local surjectivity of ring sheafification extends constant-scalar
linearity to all local scalars. Reflection of isomorphisms gives a module natural isomorphism.

The coefficient square is proved after every finite projection. The proved
`exists_scalarInverseImageIndependent` exchanges inverse image and coefficient extension;
composition of scalar-extension adjunctions reassociates the tensor products. Composing these
comparisons and the proved `constantPresentationIso` yields precisely the required functors.
All added helpers are private and proved. All added imports are private proof imports.
The full file compiled on the project server in 25.1 seconds; the sole line-length warning
was corrected before delivery. The delivery command rechecks the final file. The node's
proof and proof dependencies were updated to record this argument; no public API changed.

The proof reuses supporting private declarations from `SfbPerfectModelComplexComparison`,
`AdicPerfectModelCompleteReduction`, `GeometricInverseImageConstantModule`, and
`CompletedPullbackAdjunction` through `import all`. In particular it uses the latter's general
`pull_finiteLimits_of_isIso`, not its Noetherian completed-adjunction specialization.
`lem-sf-constant-inverse-image-scalar-normalization` is used as a tool from another unit because
it supplies the exact normalization equation for the fixed `InverseImageData.constants`.
`lem-per-independent-scalar-inverse-image` is a proved general scalar-exchange tool; it requires
no flatness assumption. The integral-models unit route is unchanged.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.Scheme.sfbImmersion_constantModuleComparison`
(`lem-sfb-adic-immersion-constant-module-comparison`). No `sorry` remains in the item module;
no holes or split-off statements were added. This is a proof from existing declared dependencies,
including the existing admitted `constantInverseImageScalarNormalization` and
`inverseImageData_exists`, rather than a claim that all transitive dependencies are axiom-free.

The argument is uniform in all modules and linear maps. In particular it imposes no nonzero-ring,
nonempty-site, Noetherian, boundedness, finite-presentation, or perfectness hypothesis; it covers
`I = 0`, `I = A`, the zero coefficient ring, and the empty scheme.

## No longer needed

The planned direct dependency
`lem-weil-pbc-site-module-sheaf-constant-ring-equivalence` is replaced by the proved ordinary
completed realization comparison and the direct constant-object argument. The planned direct
`lem-weil-pbc-algebraic-inverse-image-tensor-comparison` is replaced by
`lem-per-independent-scalar-inverse-image` and scalar-extension composition. Neither old
proof-dependency module was explicitly imported by the original item, so no import was removed.
These nodes may remain transitively needed elsewhere; no module withdrawal or global pruning is
claimed. All original public imports remain because they define the statement's functors.

## Where the brief, the DAG or earlier work was wrong

No statement repair was needed. The original plan did not expose the compatibility required for
the chosen natural constant-ring comparison: `F.constants` must fix constant scalars. The existing
scalar-normalization theorem provides that missing equation. The completed source-normalization
part was already proved as the private ordinary comparison used by the completed-model complex
comparison, so it did not need another split.

## Second reading by W6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
