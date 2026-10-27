## What changed

Constructed `Expression.ordinaryReduction` independently of realization comparisons: identity on
inputs, normalized pullback reduction, the geometric mate for proper image, inverse fixed open
reduction, and ordinary tensor reduction. Compact support uses its actual open/proper word.

Proved `ordinaryExpressionNormalization` by expression induction. The proof transposes the actual
primitive quotient augmentations and the proper-image mate. The open step uses the prescribed
`openNormalization` equation and the proved invertibility of the fixed open-reduction mate.

The item now combines the ordinary generator diagrams by cases on `BasicPair`. Geometric and open
units/counits use existing proved generic mate identities; inverse isomorphism squares follow
by cancellation. Naturality of the reduction/limit Hom equivalence and the supplied source
completion isomorphism then give the original realization equation. The statement is unchanged.

The remaining diagrams are stated in four modules: forward canonical isomorphisms, proper/open
interchange, geometric exchange/projection, and compactification composites. They concern explicit
ordinary coefficient maps and contain no comparison family, recursion-law hypothesis, completion
map, or completion inverse. Each covers only its listed part of the argument.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.IntegralSystemRealization.integralBasicGeneratorSquare` (1 of 1).
Proved the new `ordinaryExpressionNormalization` and all private combination lemmas without holes.
The delivery is a decomposition, not a foundational proof of generator coherence: four holes are
added, for a textual net of minus three:

- `WeilConjectures.IntegralSystemRealization.ordinaryCanonicalIsoSquare`
  (`lem-sf-integral-ordinary-canonical-iso-square`).
- `WeilConjectures.IntegralSystemRealization.ordinaryProperOpenSquare`
  (`lem-sf-integral-ordinary-proper-open-square`).
- `WeilConjectures.IntegralSystemRealization.ordinaryExchangeProjectionSquares`
  (`lem-sf-integral-ordinary-exchange-projection-squares`).
- `WeilConjectures.IntegralSystemRealization.ordinaryCompactificationSquares`
  (`lem-sf-integral-ordinary-compactification-squares`).

Remote `lcompile.py` accepted the explicit coefficient construction and all four statement modules.
It also accepted the normalization theorem and the original item together (exit code 0).
The generic case/cancellation helpers passed a separate isolated compile; its temporary probe
source has been removed. The original `hl` hypothesis is retained verbatim.

No definition contains a hole. No existing shared module outside the assigned item is changed.
The remaining statements use the independently prescribed ordinary and system arrows; none
asserts equality detection after finite evaluation.

## No longer needed

No existing import is removed and no module is withdrawn. The item's original five planned
proof dependencies are not applied directly: `lem-sf-primitive-reduction-transpose`,
`lem-sf-integral-expression-recursion`, `lem-sf-integral-basic-realization`,
`lem-sf-generator-reduction-coherence`, and `lem-weil-pbc-ringed-exchange-tensor-coherence`.
The proof instead uses the primitive quotient augmentation equations and existing proved generic
mate identities, together with the four smaller ordinary diagrams. The expression-recursion and
basic-realization modules remain public dependencies of the existing assembly-data module, which
is unchanged. Ringed exchange/tensor coherence remains in the proof plan of the new ordinary
exchange/projection node. Consequently none of those underlying modules is claimed globally pruned.

Removed the unused proof imports of TensorAdjunctionReductionSquares,
PrimitiveQuotientAugmentations, OpenReconstructionEffectivity and
PurNormalizedReconstructionAdjunctionCalculus from the new data module; they are used only in the
proof modules where needed.

## Where the brief, the DAG or earlier work was wrong

The planned application of `generatorReductionCoherence` is not a direct application to this
signature. Its `Word` language has no compact-support constructor, uses a different proper-image
interpretation, and bounds the entire word length by three. This item permits arbitrary child
expressions and uses `AmbientModels`, which does not supply the `unitReduction` and
`unitNormalization` fields required to construct `GeneratorReduction.Operations`. The already
proved generic ordinary mate lemmas in its implementation do apply and are reused.

The new normalization theorem completes the comparison/completion recursion once, independently
of every structural generator. The unresolved work is explicitly restricted to ordinary
coefficient diagrams. Edge cases checked at the statement level: repeated variables use both
tensor slots; identity morphisms use the same adjunctions; empty opens and zero inputs use the
same fixed open-reduction isomorphism; no cartesianness is added to proper exchange; no inverse of
projection, exchange, or target completion is assumed. An empty input family has no expression
in this syntax, so its universal clauses are vacuous.

The unrestricted normalized-reconstruction theorem is used as a general tool to obtain the unit
isomorphism on a good total limit. It is not a replacement for a unit-level proof route.

## New nodes

`def-sf-integral-ordinary-expression-reduction` records the actual ordinary tensor and proper mate
comparisons and the finite coefficient recursion. All data are explicit constructions.

`lem-sf-integral-ordinary-expression-normalization` records the proved expression-induction
normalization theorem, with no generator hypothesis.

`lem-sf-integral-ordinary-canonical-iso-square` records only the forward ordinary coefficient
squares for the listed canonical isomorphisms. The item proves inverse closure separately.

`lem-sf-integral-ordinary-proper-open-square` records only the ordinary proper/open gamma diagram.

`lem-sf-integral-ordinary-exchange-projection-squares` records the two proper geometric mate
diagrams, independently of compactification and realization.

`lem-sf-integral-ordinary-compactification-squares` records the two fixed composite diagrams,
whose proposed proofs paste the preceding primitive ordinary diagrams.

All six nodes retain the item's chapter and unit. No change record is needed: no existing
signature, definition, public import, attribute or shared consumer is changed.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
