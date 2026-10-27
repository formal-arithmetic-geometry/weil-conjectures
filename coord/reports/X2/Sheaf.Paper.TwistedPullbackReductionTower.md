## What changed

Replaced the hole in
`WeilConjectures.SpTwistedPullback.twistedPullbackReductionTower` with a complete
assembly proof. It uses the existing `integralPullbackSystemComparison` for the
actual pullback normalization and its representative equation. A private, explicit
natural comparison combines reduction/tensor, reduction/shift and that pullback
comparison; its proved component API identifies it with `nativeComparison`.
The cofinal-model construction supplies the finite-source transport and its
component equation. Composing these comparisons gives the required q and proves
its stipulated component formula.

The reconstruction proof uses the actual NX adjunction unit and the realization
equivalence's unit maps. Intrinsic completeness implies the legacy completeness
predicate; NX.unit_isIso then applies. Naturality is proved by composing natural
transformations. Private proved helpers handle functorial pairing, reconstruction
through an equivalence, and finite-field characteristic. The original theorem
signature and all original public imports are unchanged. No existing definition
or intermediate statement changes.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.SpTwistedPullback.twistedPullbackReductionTower`: 1 of 1 original
holes, with zero sorry in its module. This is a decomposition: three public
statements are split off, each with proof exactly `:= by sorry`:

- `WeilConjectures.SpTwistedPullback.twistedPullbackCofinalModels`:
  simultaneous strict cofinal models, counit-normalized reduction, pullback and
  tensor comparisons, and their functorial native finite-source transport with
  its prescribed component equation. The transport naturality and component
  normalization remain part of this construction hole.
- `WeilConjectures.SpTwistedPullback.twistedPullbackTateReduction`:
  normalized first and signed ordinary Tate-line reduction, its generator
  formulas, K-flatness and derived level formulas.
- `WeilConjectures.SpTwistedPullback.twistedPullbackLineMembership`:
  constructibility of signed-line tensor in the fixed integralClosed model.

Each statement is a proper part of the parent argument. The cofinal construction
has no completed pullback comparison, constructibility claim, TateReduction or
reconstruction unit. The other two statements respectively construct just the
normalized line record and prove just membership after line tensor. Their
sources and complete proofs in words are in their docstrings and DAG nodes.
Negative, zero and positive powers, equal quotient indices, and the empty scheme
are included in those constructions. Net holes closed minus added in this packet
is -2, before any baseline closure changes. No proof without new assumptions is
claimed.

## No longer needed

Removed private proof imports from the item:
`Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`,
`Sheaf.CategoryTheory.SystemLevelLeftExtension`,
`Sheaf.Paper.IntegralOperationsPreserveConstructible`,
`Sheaf.Paper.PurTwistSheafLocallyFree`, and
`Sheaf.Algebra.Homology.OrdinaryLineDerivedScalarComparison`.
The integral-operations theorem remains used through the retained public
interface, so its node remains a direct proof dependency. The DVR, system-level
extension, line local-freeness and ordinary derived scalar-comparison results
remain prerequisites of the new construction statements; their nodes record
these dependencies. They are not withdrawn.

The parent no longer directly uses
`lem-pur-normalized-scalar-comparison-realization`: the existing
`lem-pod-integral-pullback-system-comparison` already supplies its exact native
pullback comparison and representative equation. The former node is removed
from the parent's proof dependencies. Its module is not imported here. The
parent's line-restriction and twist prerequisites now occur under the smaller
construction steps. No existing module or declaration is deleted, and no
whole-library pruning is claimed: other parents and retained public imports
can still need them. Nothing under WeilConjectures is changed.

## Where the brief, the DAG or earlier work was wrong

The native pullback-system comparison is a closer fit than the DAG's route
through identity coefficient extension and normalized scalar realization.
The DAG also lacked a declaration supplying the simultaneous strict cofinal
models and their functorial source comparison, and membership for the particular
integralClosed tensor presentation. These are now explicit construction steps.
The cofinal-model statement groups its native finite-source transport with the
records that determine that transport. TateReduction is an existential output
of the original signature and must be supplied although the comparison assembly
does not inspect its fields. No existing statement is changed or disputed.
The unit's realized route is preserved.

## New nodes

`lem-sp-twisted-pullback-cofinal-models`, module
`Sheaf.Paper.TwistedPullbackCofinalModels`: strict reduction models and their
normalized cofinal transport, including finite-source naturality.

`lem-sp-twisted-pullback-tate-reduction`, module
`Sheaf.Paper.TwistedPullbackTateReduction`: signed-line normalization.

`lem-sp-twisted-pullback-line-membership`, module
`Sheaf.Paper.TwistedPullbackLineMembership`: signed tensor preservation.

All three inherit chapter sec-smooth-purity, unit sk-prop-sp-integral-adjunction,
and blueprint ancestry through the original item to
`det-sp-integral-adjunction-bijection`. No change record is required because no
existing public statement, definition or public import changes.

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
