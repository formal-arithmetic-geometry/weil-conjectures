## What changed

Replaced the sole proof hole of `WeilConjectures.GeneratorReduction.primitiveQuotientAugmentations`
with a complete assembly from three strictly smaller calculations, in three new modules:
`Sheaf.SixFunctors.TensorQuotientAugmentationOnGood`,
`Sheaf.SixFunctors.PullQuotientAugmentationOnGood`, and
`Sheaf.SixFunctors.FiniteReductionCompletionUnit`.
The public statement and public import of the assigned module are unchanged.

The tensor calculation is a strict Roos-coordinate equation on good complexes. The
assigned module separately cancels the ordinary tensor representative and the reference
Roos isomorphism, using `Tensor.canonical.2` and the defining property of the existing
global tensor model. For pullback it separately combines `Pull.model`, naturality of
the actual completion unit, and its defining representative equation, then cancels the
reference Roos model. These are actual compositions and cancellations in Lean, rather
than applications of new lemmas restating the final clauses.

The existing resolving-class localization theorem supplies an isomorphic good complex
for every derived object. Naturality of both sides extends the equations to all objects,
with product isomorphisms for tensor. Finite reduction of the completion unit is
transported through `reductionEvaluation`; joint conservativity gives invertibility
of the whole reduction. Both primitive maps are this unit followed by their existing
comparison isomorphism. Their reductions are therefore invertible.

Added only private proved helpers to the item, and proof imports (including
`import all Sheaf.Paper.IntegralOperationsWellDefined` to use its existing private
resolving-class localization proof). No existing definition or signature was changed,
no consumer requires adaptation, and no change record for an interface repair is needed.
The node proof and proof dependencies now describe this actual argument.

## Proved and sorry left

Closed the original hole:
`WeilConjectures.GeneratorReduction.primitiveQuotientAugmentations`.
There are zero direct holes left in the assigned module.

Three holes are added, each the entire proof of one public theorem in its own module:

- `WeilConjectures.GeneratorReduction.tensorQuotientTranspose_onGood`
  (`lem-sf-tensor-quotient-augmentation-on-good`): the strict balanced tensor
  transpose computation on flat-term K-flat inputs, before global-model cancellation.
- `WeilConjectures.GeneratorReduction.pullQuotientTranspose_onGood`
  (`lem-sf-pull-quotient-augmentation-on-good`): the strict ordinary pullback
  transpose computation on a good input, before the completion-unit/model calculation.
- `WeilConjectures.GeneratorReduction.finiteReduction_completionUnit`
  (`lem-sf-finite-reduction-completion-unit`): finite scalar extension of the actual
  quotient completion unit is invertible, with no geometric or completeness hypotheses.

This is a decomposition: one original hole closed and three lower holes added, not
an axiom-free completion of the mathematical result. All private helpers are proved.
No definitions contain new holes. Each new theorem has its source and a full proof
in words in its docstring and node.

Edge cases: all schemes, arbitrary morphisms (not just opens), and unbounded inputs
remain allowed. The good representatives have flat terms with no cohomological bound.
The formulas include the empty scheme, zero input complexes, n=0 (exponent one), and
zero tensor factors. Finite reduction of completionUnit does not assert that the
unreduced unit is invertible. The transpose statements are equations in the full
Roos model, with zero shifted coordinate; finite evaluations are used only to detect
invertibility, never equality of derived-system maps.

Validation: remote compilation of all four modules and the delivery preflight.

## No longer needed

No imports were removed, no modules were withdrawn, and no global pruning is claimed.
The finite-unit module retains the canonical bridge import, whose exported instances
are needed to resolve the published coefficient universes. The original module had only the
public canonical-bridge import; it remains necessary
for the statement. Its three new imports supply exactly the three calculations used.

The item's direct proof dependencies no longer include
`lem-coef-sequence-adjunction-cochain-transposes` or
`lem-pur-integral-operation-roos-effectivity`. The former remains needed in the two
new representative transpose nodes. For invertibility the proof uses the more general
finite-reduction statement for the actual completion unit, whose route uses the
existing generic `lem-coef-normalized-dvr-roos-finite-reduction`, rather than proving
operation-specific effectivity again. The old operation effectivity declaration is
preserved and may have other consumers. The original bridge, tensor, pullback,
calculus and full Roos-model dependencies remain, directly or through the new nodes.
No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement was identified. The prior node compresses the comparison of
strict representative maps, the localization descent, and finite invertibility into
prose. The supplied declarations fix the appropriate models, but do not directly
state the two needed strict transpose calculations or finite invertibility of this
particular completion unit. These calculations are isolated below the original
obligation; its model cancellation, naturality descent and conservativity argument
are now formal Lean proofs.

The first delivery preflight detected a transitive cycle in its baseline prose DAG
through the canonical bridge, purity conventions, Frobenius transport and generator
reduction. During the subsequent audit the shared repository received dependency
corrections to the conventions and realization routes. Rechecking the refreshed DAG
finds no return path from either new transpose node to this item. No unrelated DAG
repair or Lean interface change is included in this packet. The actual Lean import
direction to the existing resolving-class proof was checked and is allowed.

Existing alternative completion normalization and reconstruction interfaces found
by local search often require l invertible on the scheme or select a different
calculus/presentation. The assigned theorem quantifies over arbitrary schemes and
the supplied canonical models, so those extra assumptions were not introduced.

## New nodes

`lem-sf-tensor-quotient-augmentation-on-good` records the strict tensor transpose,
with simultaneous representative normalizations, both Roos coordinates and an exact
Lean signature. Its consumer additionally proves global model cancellation and
naturality descent. It neither asserts the final tensor conjunction nor its
invertibility.

`lem-sf-pull-quotient-augmentation-on-good` records the strict pullback transpose,
independent of the supplied RingedModels record; it takes only the pull presentation
and the actual realization needed for the representative calculation. Its consumer
proves the completion-unit/model equation and global cancellation and descent.

`lem-sf-finite-reduction-completion-unit` records the generic finite invertibility
of the actual quotient unit. Its consumer proves whole-system invertibility and
applies it to both primitive comparisons. Its proof plan uses normalized quotient
towers, finite Roos effectivity, the scalar triangle identity and representative
naturality. Searches of Mathlib by LeanSearch, LeanFinder, Loogle and grep, together with local
search through the existing completion interfaces, found no matching unrestricted
statement for this unit.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
