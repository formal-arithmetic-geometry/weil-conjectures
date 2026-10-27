## What changed

Replaced the proof of `WeilConjectures.OpenQuotientCompletion.openQuotientCompletionUnitComparison`
with a categorical assembly. All existing declarations, signatures, structure fields,
public imports and definitions are unchanged.

The proof constructs the operation presentation using the existing
`IntegralOpenReduction.normalizedOpenSections` and
`OpenSemilinearTensor.openCoefficientOperationsExistence`. It uses three separate
component statements, in new modules:

- `Sheaf.SixFunctors.OpenStrictQuotientDescent`: strict augmented tensor descent for a
  supplied coefficient/operation presentation, before inverse limits.
- `Sheaf.SixFunctors.OpenNormalizedRoosRestriction`: signed Roos comparison and its
  compatibility with the constant-tower adjunction unit, independently of quotients.
- `Sheaf.SixFunctors.OpenExactPullbackLocalization`: ordinary module pullback and
  slice restriction, normalized on the actual adjunction's graph generators.

The derived tower comparison is constructed using Mathlib `leftDerivedNatIso`;
`leftDerivedNatTrans_app` proves its universal-counit normalization. The proof then
constructs `constantPull`, proves its normalization by cancellation, and proves
`completedComparison` by naturality at the quotient augmentation. Naturality of
lambda and the constant-tower unit equation give `alpha_eq`. Functoriality and the
strict augmentation square give `b_alpha`, and composition gives `rho_unit`.

The three new modules import the existing augmented-completion interface. Their
remaining statements have complete source-based proof plans and edge-case checks.
The item's DAG proof and proof dependencies now match this assembly. No existing
module other than the assigned item is changed.

## Proved and sorry left

Closed the item's one original hole:
`WeilConjectures.OpenQuotientCompletion.openQuotientCompletionUnitComparison`
(node `lem-sf-open-quotient-completion-unit-comparison`). The item itself has zero
remaining holes.

Added three holes, each the whole proof of a named theorem in its own module:

- `WeilConjectures.OpenQuotientCompletion.openStrictQuotientDescent`
  (`lem-sf-open-strict-quotient-descent`).
- `WeilConjectures.OpenQuotientCompletion.openNormalizedRoosRestriction`
  (`lem-sf-open-normalized-roos-restriction`).
- `WeilConjectures.OpenQuotientCompletion.openExactPullbackLocalization`
  (`lem-sf-open-exact-pullback-localization`).

This is a decomposition: one upper hole closed, three strictly smaller holes
added, net minus two. It does not claim a complete proof of the underlying open
localization or Roos theory. No data is defined by choosing an arbitrary witness
from these statements; their witnesses are eliminated only inside the theorem proof.

## No longer needed

None. No original import, node or module is withdrawn or declared obsolete.
The original mathematical dependencies are retained in the smaller components'
proof plans; the parent's direct proof dependencies now cite those components
and the existing coefficient-operation construction. Existing public imports are
retained for compatibility. No unit statement or unit proof step is bypassed.

The related `OpenTensorQuotientCochains` and `OpenTensorQuotientGeometry` statements
were inspected but do not supply these interfaces: they impose Noetherian,
constructibility and tied-universe assumptions absent from this item.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or marked disputed. The original plan did
not provide a specialized Lean declaration assembling the pinned strict, signed
Roos and graph-normalized ordinary pullback interfaces. The new nodes isolate
that missing glue without replacing the original theorem by an equivalent hole.
In particular the Roos component's final equation concerns the constant-tower
adjunction unit, and `alpha_eq` is proved from it using naturality rather than
being assumed under another name.

The rework row was checked before writing. Its quarantined source agrees with
the assigned original module and has been preserved; no path is withdrawn and
no quarantine archive is edited.

## New nodes

`lem-sf-open-strict-quotient-descent` formalizes the tensor, transition,
K-flat-computation and strict-augmentation portion of original steps 1–4, for an
already supplied operation presentation. Source: Stacks 099N, 0G7E and 07A4.

`lem-sf-open-normalized-roos-restriction` formalizes the exact-product signed
Roos comparison and constant-tower unit compatibility from original step 5.
Source: Stacks 0940, 0941, 07KC and 099N. The quotient-specific equation is proved
in the item.

`lem-sf-open-exact-pullback-localization` formalizes only the ordinary,
graph-normalized ringed localization from step 7. Source: Stacks 03D2, 00VC,
09BN and 099N. The derived tower comparison is proved in the item.

LeanSearch, LeanFinder, Mathlib grep and both project roots were searched; the
records include the actual search results. Blueprint searches found only broader
quotient and Roos statements, and no duplicate of the ordinary ringed interface.
Each new statement was checked at identity and empty opens, zero complexes,
exponent one where applicable, and arbitrary unbounded complexes. No change
record is required: no existing statement, definition, visibility, instance,
attribute or public import changes.

## Second reading by Y8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
