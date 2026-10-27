## What changed

Reduced `WeilConjectures.PurityIntegration.compositeIntegrationCounit` to two strictly
smaller native-map calculations. The main module performs the inverse compositor /
projection calculation, identifies the resulting coefficient with `compositeTrace`,
converts between the two braiding conventions, and derives both the unit value and the
naturality square. It then specializes the assembly to the two sites.

Moved the existing operation definitions and five proved normalization theorems
verbatim to `Sheaf.Paper.CompositeIntegrationOperations`, publicly reexported by the
original module. This avoids an import cycle when the intermediate lemmas use the
operation definitions. No definition, native map, public signature, target, or domain
changed. A parser comparison verifies that all 31 moved declarations have byte-identical
signatures and bodies, and that the main theorem signature is unchanged.
The change record is `coord/changes/A8-composite-integration-operations.md`.
The two new proof dependencies are private imports of the original module.

Validation: all four delivery modules compile together. The unchanged direct consumers
`AffineOrderedIntegrationTransposes` and `ProjectionPurityAgreement` compile individually
against the extracted definitions (33.2 s and 9.8 s). The final assembly compiled alone
in 6.9 s. Consumer copies used for these checks are excluded from the delivery.

## Proved and sorry left

Original holes: 1. The body of `compositeIntegrationCounit` is complete relative to its
two new dependencies. This is a decomposition, not a completed proof of the original
mathematics: one upper hole is replaced by two lower holes (net minus one).

The only remaining holes in this delivery are:

- `WeilConjectures.PurityIntegration.nativePrecompositorContraction`, node
  `lem-pur-native-precompositor-contraction`, in `NativeIntegrationContraction`.
  This is the successive trace-contraction calculation before projection/compositor
  cancellation. Its proposed proof does not use `projection_comp` or the fg projection.
- `WeilConjectures.PurityIntegration.nativeIntegrationProjectionLaws`, node
  `lem-pur-native-integration-projection-laws`, in `NativeIntegrationProjectionLaws`.
  This is inverse projection naturality and unit normalization for arbitrary coefficient
  objects, without any twisted adjunction or composite counit conclusion.

The relocated normalization theorems retain their complete proofs. There are no holes
in definitions, no new data choices, and no assumptions hidden in private helpers.

## No longer needed

No mathematical dependency or module is pruned. The original public imports are
preserved transitively through `CompositeIntegrationOperations`. Removed the unused
private import `Sheaf.Paper.ExchangeProjectionSuppliedDomains` from the operation
presentation; no declaration refers to its supplied-domain API. The parent's direct proof edges to `def-exchange-projection`,
`def-weil-pbc-composite-adjunction`, and `lem-pur-tensor-action-trace-contraction` now
belong to the two native-map steps, where their facts are used. None is withdrawn or
claimed to be mathematically unnecessary. No source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The existing `IntegrationOperations` record stores components but not naturality,
monoidal coherence, or compatibility with braiding. Consequently the existing generic
`tensorAction_trace_contraction` cannot be applied to that record alone. The new
contraction statement is specialized to the actual native site maps, whose published
natural transformations and pullback tensor comparisons provide these laws. This
matches P7's report of the remaining gap.

The DAG unit argument `q=q²` also needs naturality and canonical unit comparisons; an
arbitrary list of component maps does not supply those. The native projection-law
lemma states exactly the required inverse naturality and unit normalization, rather
than asserting them for arbitrary records. The ordinary-site unit theorem already
exists as `Etale.projectionMap_rightUnitality`; the pro-etale construction uses the same
proper-counit/open-tensor calculation. No statement dispute or unit-route change is
claimed.

Edge cases were checked in the typed calculation: empty supplied domains, zero trace
maps, identity functors and comparison maps, the tensor-unit coefficient, and arbitrary
(not necessarily invertible) coefficient arrows. Unit normalization is only asserted
when the particular projection component is invertible; naturality only assumes the
two components that it inverts. The precompositor formula retains every pullback and
compact-support comparison and the actual composite-adjunction counit.

## New nodes

`def-pur-composite-integration-operations` attaches the existing typed operation
presentation to its new shared module. Its declarations and proofs are moved verbatim;
this is not a new realization or an arbitrary witness construction.

`lem-pur-native-precompositor-contraction` is the first contraction calculation in the
parent's route, with the fg projection/compositor cancellation explicitly excluded.
The existing generic contraction theorem remains its main dependency.

`lem-pur-native-integration-projection-laws` records two laws about the actual inverse
projection, independent of the chosen twisted adjunctions. It supplies precisely the
parent's tensor-unit and naturality assembly steps.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
