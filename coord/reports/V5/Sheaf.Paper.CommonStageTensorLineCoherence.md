## What changed

The statement of `WeilConjectures.commonStageTensorLineCoherence` and its public import
are unchanged. Its proof now assembles the canonical associators and right unitors
with `NatIso.ofComponents`. Bifunctoriality supplies naturality of tensoring the
regular-unit identification.

Added three modules. `CommonStageTensorLineCoherenceNaturality` states naturality
of the prescribed associator. `CommonStageTensorRightUnitorNaturality` states
naturality of the prescribed right unitor. `RegularCoefficientCoherentReduction`
proves the identification of the reduction of the regular completed coefficient
with the coherent tensor unit. For the latter, compare ordinary tensor units via
uniqueness of left adjoints, then use preservation of tensor by reduction and
the invertible counit at the reconstructed unit. This avoids constructing the
regular quotient tower again. Full faithfulness lifts the resulting isomorphism;
localization and the least-stage inclusion identify the specified zero twist.
All imports added to the original item are private proof imports.

## Proved and sorry left

Closed the original one hole, `WeilConjectures.commonStageTensorLineCoherence`,
by a complete assembly from named statements. Proved the new helper
`WeilConjectures.regularCoefficient_coherentReduction` with no new hole.

Two new holes remain, each the entire proof of a strictly smaller constraint
naturality equation:

- `WeilConjectures.commonStageTensorAssociator_naturality`, node
  `lem-pur-common-stage-tensor-associator-natural`.
- `WeilConjectures.commonStageTensorRightUnitor_naturality`, node
  `lem-pur-common-stage-tensor-right-unitor-natural`.

Thus this is a decomposition: one original hole closed, two holes added, zero
holes left in the item itself. Neither helper asserts the existence of the
natural isomorphisms in the item; the item supplies their actual components,
assembles their naturality and proves the specified regular-unit identification.
The associator helper concerns only the canonical associator equation, and the
unitor helper concerns only the reconstructed unit, not the zero twist.

Edge cases: all objects and arrows are arbitrary, including zero objects, zero
arrows and identities; no finite Tor-amplitude or nonempty-scheme condition was
introduced. The regular-unit proof is categorical and remains valid on the empty
scheme. Least-stage inclusion uses exactly the field in the definition of the
specified zero twist. The blueprint unit `sk-prop-an` has no realized nodes and
its route is preserved.

## No longer needed

No original public or private import was removed. No module is withdrawn, and no
whole module is claimed pruned.

The item's direct proof no longer invokes `lem-pur-completed-line-complete`
(`Sheaf.Paper.CompletedLineComplete`): tensor preservation and the reconstructed
unit counit replace the proposed completeness argument for the regular unit.
This is a dependency removal from this item's argument, not a claim that the
module is globally unused.

`def-weil-linear-scalar-localization` and
`lem-coef-completed-tensor-scalar-linearity` move from the item's direct proof
into the two constraint-naturality obligations; they are still needed there.
The remaining original dependencies are retained directly or by those helpers.

## Where the brief, the DAG or earlier work was wrong

The existing `DerivedPullbackTensorIso` declarations provide canonical objectwise
associators and unitors but do not state their naturality in coefficient objects.
The two new nodes isolate those missing equations. They retain the original
integral reduction, rational localization and common finite-stage argument;
there is no reliance on faithfulness of separate finite evaluations.

The regular-unit part admits a shorter categorical proof than the planned
explicit coefficient-tower calculation. No existing statement or definition was
changed, and no source-library declaration was modified.

## New nodes

`lem-pur-common-stage-tensor-associator-natural` is the three-arrow naturality
square for the fixed associator, with an integral/reduction, rational and common-stage
proof in words. Its module is `Sheaf.Paper.CommonStageTensorLineCoherenceNaturality`.

`lem-pur-common-stage-tensor-right-unitor-natural` is the one-arrow naturality
square for the fixed right unitor at the reconstructed common-stage unit. Its
module is `Sheaf.Paper.CommonStageTensorRightUnitorNaturality`.

`lem-pur-regular-coefficient-coherent-reduction` identifies the coherent reduction
of the regular completed coefficient with the system tensor unit. Its module is
`Sheaf.Paper.RegularCoefficientCoherentReduction`, and its proof is complete.

All three inherit chapter `sec-smooth-purity`, unit `sk-prop-an` and the blueprint
ancestor `det-def-sp-tate-twist-locally-free`, proof (3), final sentence, via the
item node. Mathlib searches are recorded from the actual msearch results; they
find abstract monoidal naturality and unrelated adic-completion declarations,
not the prescribed derived coefficient constraints. No change record is needed:
all existing signatures, definitions and public imports stay unchanged.

## Second reading by V5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
