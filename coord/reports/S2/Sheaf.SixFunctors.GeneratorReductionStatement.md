## What changed

Repaired `WeilConjectures.IntegralSystemRealization.RingedModels` in
`Sheaf.SixFunctors.IntegralSystemCanonicalBridge`: its new `tensorRepresentative`
field identifies the supplied ordinary tensor representative with the calculus's
K-flat tensor representative, after `tensorClosed`. Equality of functors alone
left a scalar ambiguity that invalidated the primitive tensor transpose formula.
The canonical functors, every existing field, and all target signatures remain
verbatim. This is a definition repair, with zero holes added to the definition.
The consumer and DAG-citer audit is in
`coord/changes/S2-generator-tensor-representative-normalization.md`.

Replaced the body of `GeneratorReduction.primitiveReductionTranspose` by a complete
Lean combination of the constructor cases. The length bound forces all children
to length zero. Proper image uses its defining counit; the open transpose is the
inverse Hom-equivalence identity; both inverse laws are proved by functoriality
and cancellation. Tensor and pullback follow by transposing their quotient
augmentation equations and cancelling the invertible reduced completion map.

The two genuinely separate representative/effectivity subresults are stated in
`Sheaf.SixFunctors.PrimitiveQuotientAugmentations` and
`Sheaf.SixFunctors.OpenReconstructionEffectivity`, imported privately by the item.
They refer only to the underlying canonical bridge, so no definition extraction
or import reversal is necessary. The original item statements are unchanged.

Validation: `lcompile.py --all` compiled all four packet modules and eight
unchanged direct consumers against the repaired bridge (twelve modules, exit
code zero). The unchanged consumer overlays were removed after this check; no
consumer adaptation is needed.

## Proved and sorry left

Original item: three named holes. One upper hole is closed by a decomposition;
two original holes remain. Two named lower holes are added. This is **a
decomposition, not a net proof**: closed minus added is 1 - 2 = -1.

Closed upper hole:
- `WeilConjectures.GeneratorReduction.primitiveReductionTranspose`
  (`lem-sf-primitive-reduction-transpose`): its proof has no `sorry`; it uses the
  two lower statements and the proved elementary adjunction/word arguments.

Original holes left unchanged:
- `WeilConjectures.GeneratorReduction.completionMap_isIso`
  (`lem-sf-generator-reduction-coherence`).
- `WeilConjectures.GeneratorReduction.generatorReductionCoherence`
  (`lem-sf-generator-reduction-coherence`).

Holes added, each a public theorem with exactly a `by sorry` body:
- `WeilConjectures.GeneratorReduction.primitiveQuotientAugmentations`
  (`lem-sf-primitive-quotient-augmentations`): the whole-representative tensor
  and pullback augmentation equations and invertibility of their reductions.
- `WeilConjectures.GeneratorReduction.openReconstructionEffectivity`
  (`lem-sf-open-reconstruction-effectivity`): invertibility of the supplied
  canonical open mate and the actual reconstruction unit on the needed domain.

No `sorry` occurs in a definition or private helper. The bridge repair adds zero
holes. The packet has four remaining holes in total (two original and two new).

## No longer needed

No module or node is withdrawn. No original public or private import is removed.
The primitive proof no longer directly needs the separate cochain-transpose,
completed-primitive-counit, or Roos-effectivity tool uses in its old proof plan;
the representative and effectivity work is localized in the two new statements.
These foundations remain dependencies of the lower argument and are **not**
claimed as globally pruned. The old direct `tool_uses` approvals on the primitive
node are removed accordingly. The square nodes remain needed for the still-open
main theorem, so zero current Lean uses is not treated as a withdrawal reason.

## Where the brief, the DAG or earlier work was wrong

The old `RingedModels.tensorClosed` field equated tensor functors without
identifying their representative comparisons. Negating the ordinary tensor
representative and the completion comparison preserves `Tensor.canonical` and
all old bridge fields, but negates `tensorCompletion` and its coefficient map.
Thus the independently supplied comparison was not pinned to the calculus's
normalization. The new representative equation repairs this omission, matching
the blueprint's canonical ringed maps. The bridge node records the correction
and all 31 DAG citers were audited.

The primitive node's plan described the scalar-adjunction argument correctly,
but the existing Lean dependency interfaces do not directly state the required
augmentation equalities for the supplied normalized model. Roos effectivity
asserts invertibility of scalar adjoints of projections; it does not identify
those projections with the independently supplied completion maps.
`integralOpenReductionComparison` supplies an existential normalized model,
whereas the item needs the assertion for its given `RealizationModel`. The new
statements isolate exactly these representative identifications.

Further issues for the retained main hole: its primitive helper only covers
length at most one whereas endpoints can have length three; the square modules
import this item for its definitions; and `StructuralSquares` in the open-square
module has no length bound whereas the tensor-square theorem is stated only for
length at most three. No signature was silently altered to conceal these gaps.

## New nodes

`lem-sf-primitive-quotient-augmentations` isolates the strict quotient/Roos
augmentation computation for tensor and pullback. Its conclusion mentions
neither expression words, the recursive primitive predicate, nor generator
squares. The consumer proves the transpose algebra itself. Edge cases checked:
zero inputs, the zero scheme, identity pullback, and arbitrary unbounded inputs;
completion preserves the finite reductions even when it changes the input.

`lem-sf-open-reconstruction-effectivity` isolates open completeness and
identification of the actual adjunction mate for the given realization. Its
conclusion is solely two invertibility assertions. The open transpose and both
inverse laws are proved in the consumer. The domain includes exactly admissible
input objects and the coefficient unit; the empty open and identity open use
the same strict comparison. Both nodes have source, complete proof in words,
three search records, and Lean attachments. The existing compatibility unit's
route is retained.

Change record: `coord/changes/S2-generator-tensor-representative-normalization.md`.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
