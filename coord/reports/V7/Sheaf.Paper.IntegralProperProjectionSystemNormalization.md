## What changed

Reduced the whole-system proper projection square to three independent normalization
calculations. The direct-image square is obtained from the existing proved generic
`Adjunction.rightAdjointProjectionMap_mate`; the remaining proof pastes this square
with tensor naturality and cancels the actual identity-open isomorphism. The
pullback comparison, its direct-image mate, and both endpoint comparisons are
constructed explicitly in `IntegralProperProjectionCoefficientData`.

The original theorem statement and its public imports are unchanged. The finite-Tor
hypothesis is retained in the statement; the morphism identity does not require it.

Validation: all five delivery modules compile through the server compiler. The final
assigned module compiled in 24.1 seconds in the focused check and 56.9 seconds in
the full delivery compile. The unused-hypothesis warning was then removed without
changing the signature. Profiling options have been removed. New node signatures match
the Lean text, and proof dependency lists agree with the uses in their proof steps.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.IntegralProjectionReduction.integralProperProjectionSystemNormalization`
by a complete combination proof from three strictly smaller statements. This is a
decomposition, not a claim that the proper normalization is now axiom-free.

Added three holes, one per new module:

- `WeilConjectures.IntegralProjectionReduction.integralProperTensorPullbackReduction`:
  compatibility of the tensor and pullback comparisons, without projection maps or
  support/direct-image comparisons
  (`lem-sf-integral-proper-tensor-pullback-reduction`).
- `WeilConjectures.IntegralProjectionReduction.integralProperSupportReductionIdentity`:
  equality of two one-input comparisons, without any tensor or projection map
  (`lem-sf-integral-proper-support-reduction-identity`).
- `WeilConjectures.IntegralProjectionReduction.systemProperIdentityOpenProjection`:
  cancellation of the identity open factor, wholly in the system category and
  independent of the integral datum
  (`lem-sf-system-proper-identity-open-projection`).

The new coordinate definitions contain no holes or arbitrary existence witnesses.
Original holes: 1; closed: 1; added: 3; remaining in delivery: 3.
The textual hole count increases by two; the result is a decomposition, not a net
hole decrease.

## No longer needed

The parent no longer directly lists `def-fix-six-functor-datum`,
`lem-sf-integral-compactification-system-realization`,
`lem-pur-normalized-integral-tensor-tower`, `lem-coef-integral-residue-tor`, or
`lem-sf-integral-reductions-jointly-faithful` as proof dependencies. Their relevant
normalization work is now localized in the three smaller lemmas or in the existing
coordinate construction; this is not a claim that their modules are globally unused.

The new coordinate module imports `IntegralProjectionCoordinateData` and the smaller
`ConstructibleProjectionMates` module for the proper identity square. Its initial
import of `IntegralProjectionFiniteEvaluationData` was removed.

No original public import or existing module is withdrawn. No dependency can be
claimed globally pruned: the completed-tensor and realization constructions remain
used by the explicit coordinates and the remaining normalization statements.

The parent proof now uses the three precise normalization equations instead of
asking for the entire proper square again. The direct square itself requires no
new theorem: it is the proved generic adjunction-mate theorem. The existing
`IntegralStageProjectionStructuralIdentities` proper-coincidence theorem cannot
serve here because its import closure already contains this item.

## Where the brief, the DAG or earlier work was wrong

The prior parent proof grouped tensor-pullback compatibility, the one-input support
comparison, and system identity-open cancellation into one hole. The revised proof
makes these separate equations and supplies the intervening categorical argument.
No statement dispute, signature change, source-library edit, or shared definition
repair is made. The preflight metadata check caught a definition body accidentally
included in the new coordinate node's `lean.statement`; that field now stops before
`:=`. A change record explains the local-only proof commands flagged by the static
advisory. The warning-free delivery compile passes for all five modules.

## New nodes

`def-sf-integral-proper-projection-coordinates`, realized in
`lean/Sheaf/Paper/IntegralProperProjectionCoefficientData.lean`, constructs tensor and
pullback comparisons, their direct-image mate, and identity-open coordinates.

`lem-sf-integral-proper-tensor-pullback-reduction`, realized in
`lean/Sheaf/Paper/IntegralProperTensorPullbackReduction.lean`, states tensor-pullback
compatibility without projection or support maps.

`lem-sf-integral-proper-support-reduction-identity`, realized in
`lean/Sheaf/Paper/IntegralProperSupportReductionIdentity.lean`, states the one-input
support/direct identity without tensor or projection maps.

`lem-sf-system-proper-identity-open-projection`, realized in
`lean/Sheaf/Paper/SystemProperIdentityOpenProjection.lean`, states pure-system
identity-open cancellation without an integral-operation datum.

## Second reading by V7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
