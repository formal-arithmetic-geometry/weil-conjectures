## What changed

Moved the existing finite-word generator definitions verbatim to
`Sheaf.SixFunctors.GeneratorReductionData`, publicly re-exported by the original
module. The change record is `coord/changes/T7-generator-reduction-data.md`.

Replaced the hole in `WeilConjectures.GeneratorReduction.completionMap_isIso`
with an induction on Word. At a tensor vertex it maps the two child isomorphisms
through the ordinary tensor and composes with its primitive completion unit.
Pullback and proper image use the corresponding child map and completion or
reconstruction unit; open extension only maps the child isomorphism.

The two new proof dependencies separate the analytic input from the recursive
categorical assembly: `primitiveCompletionEffectivity` concerns only primitive
maps at integral objects, while `shortWordIntegralDomain` concerns only
constructibility and finite Tor amplitude of child values of length at most two.
They are strict parts of the proof and do not restate the recursive isomorphism.

Existing declarations, definition bodies and theorem signatures are unchanged.

## Proved and sorry left

Original item: 2 holes. One hole closed by decomposition:
`WeilConjectures.GeneratorReduction.completionMap_isIso`
(node `lem-sf-completion-map-is-iso`).

One original hole remains untouched:
`WeilConjectures.GeneratorReduction.generatorReductionCoherence`
(node `lem-sf-generator-reduction-coherence`).

Two holes added:
- `WeilConjectures.GeneratorReduction.primitiveCompletionEffectivity`
  (node `lem-sf-primitive-completion-effectivity`).
- `WeilConjectures.GeneratorReduction.shortWordIntegralDomain`
  (node `lem-sf-short-word-integral-domain`).

The previously proved `primitiveReductionTranspose` is preserved. This is a
one-to-two decomposition, not a net proof: 1 closed, 2 added, net -1 holes.
There are no holes in definitions or private helpers. The new data module has zero holes.

## No longer needed

Removed unused private proof imports from the item:

- `Sheaf.Paper.BasicOperationsCoefficientReduction`
- `Sheaf.Paper.RingedExchangeTensorCoherence`
- `Sheaf.SixFunctors.IntegralOpenReductionComparison`
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`
- `Sheaf.Paper.FiniteTorAmplitudeSites`
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`
- `Sheaf.Paper.NormalizedDVRTower`
- `Sheaf.Paper.SemilinearDerivedSections`
- `Sheaf.Paper.SfCommonStageDirectImage`
- `Sheaf.Paper.SfIntegralConstructible`
- `Sheaf.SixFunctors.OpenTensorNormalization`
- `Sheaf.SixFunctors.SemilinearProperOpenMatePasting`

No mathematical dependency or module is withdrawn. All four original public
prerequisites remain public through the data re-export. The new completion-map
proof uses primitive effectivity and the short integral domain rather than the
generator-square lemmas. Those lemmas remain needed by the untouched generator
coherence theorem; no pruning claim is made about them.

## Where the brief, the DAG or earlier work was wrong

The assigned module combines its interface and consumers. Both declared generator
square dependencies import this module, so importing them into it would form a
cycle. Their stated interfaces also differ: tensorAdjunctionReductionSquares has
length-three bounds, whereas OpenInterchangeReduction.StructuralSquares requests
an unbounded structural family for the internal clopen factorization. This packet
does not change either held dependency or pretend that the bounded theorem supplies
the unbounded family. The generator coherence hole remains explicitly reported.

Preflight caught an unnecessary dependency edge initially added from the still-open
generator-coherence node to the separately proved completion theorem. The unchanged
generator proof does not use that theorem yet, so its original proof dependencies
are retained. The completion theorem has its own node and actual dependencies.

The completion isomorphism had only a docstring attachment to the broad generator
node. It now has its own node matching the actual recursive proof.

## New nodes

`def-sf-generator-reduction-data`: the unchanged public definitions, moved to a
separate module to permit lower proof imports without cycles. Existing definition
node Lean attachments are repointed to the new module.

`lem-sf-completion-map-is-iso`: the existing completion-map theorem, with its
induction argument and its two actual proof dependencies recorded.

`lem-sf-primitive-completion-effectivity`: the actual tensor/pullback completion
units and reconstruction unit are invertible on complete constructible finite-Tor
inputs or the coefficient unit. Sources and the full representative argument are
in the docstring and node. It makes no recursive Word claim.

`lem-sf-short-word-integral-domain`: the integral values needed as children have
the input domain for primitive effectivity and open reconstruction. The bound is
two because the parent has length at most three. Its conclusion is an object
property, not invertibility of any completion map. The source, recursive proof and
edge cases (scalar unit, identity, empty open, zero inputs) are recorded.

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
