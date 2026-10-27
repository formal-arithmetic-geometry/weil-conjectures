## What changed

Proved `WeilConjectures.IntegralProjectionReduction.systemIdentityOpenEvaluation`
without changing its signature, definitions, or public import. All added helpers are
private and proved in the assigned module. No existing consumer needs adaptation.

The proof uses the existing `systemPullbackCompositorEvaluation` theorem at two
identity maps. A categorical cancellation argument shows that compatibility with
composition forces compatibility with the identity comparisons. The normalized
system unit comes from `systemPushIdentityPullUnit`. The finite unit is transported
from `upperStarComp_id_left` and localized by the proved `descend_left_unit` helper.
The prescribed `OpenEvaluation.transpose` then proves the open identity equation.
The proved generic `exact_left_id_localized` identifies the localized ordinary finite
identity-open comparison with the derived adjunction comparison.

Proof-only imports supply the compositor-evaluation theorem and the generic unit,
transport, and exact-localization helpers. The item's DAG proof and proof dependencies
now record this argument. No source-library declaration or shared interface changes.

## Proved and sorry left

Closed: the sole original hole,
`WeilConjectures.IntegralProjectionReduction.systemIdentityOpenEvaluation`
(`lem-sf-system-identity-open-evaluation`). Original holes: 1; closed: 1;
remaining in the assigned module: 0; added: 0. No split-off statement is introduced.

Validation: the assigned module compiled through `lcompile.py` in 19.5 seconds
with no warnings. Its theorem signature is textually unchanged, all lines have at
most 100 characters, and only this module and its own DAG node are included.
All temporary profiling options and scratch modules were removed.

The existing imported theorem
`WeilConjectures.IntegralSystemRealization.systemPullbackCompositorEvaluation`
(`lem-pur-system-pullback-compositor-evaluation`) remains an external proof obligation.
It is not duplicated or moved. It states general composition compatibility, and the
new combination proof derives identity compatibility and then the open mate identity.
Faithfulness is used only for a pullback functor isomorphic to the identity, never
for finite evaluation on a derived system category.

## No longer needed

No original Lean import is removed, and no module is withdrawn or globally pruned.
The public coefficient-coordinate import is needed by the unchanged statement.

The original direct proof dependencies
`def-pur-completed-pullback-tower-realizations` and
`def-pur-completed-pullback-tensor-comparison` are no longer separate steps of this
node's proof: the existing composition-evaluation theorem packages their normalization
calculation. Their definitions remain transitive dependencies. The other original
proof dependencies are retained for the bridge, units, and inverse mate.

`Sheaf.Paper.IdentityOpenSystemEvaluation` is not imported: the proof does not transfer
the hole to the parallel identity-open theorem. No tensor, compact-support, projection,
constructibility, finite-type, or boundedness result is used to detect equality.

## Where the brief, the DAG or earlier work was wrong

The original plan repeats an ordinary-section normalization calculation. It can instead
reuse the stated general pullback-compositor evaluation theorem. The extra argument is
categorical: normalize the two identity compositors, apply naturality, and cancel the
invertible comparison; then apply the actual open-unit mate equation. This closes the
assigned hole without another split in its six-times-decomposed ancestor chain.

The generic helpers from `StrictTowerDirectImageCoherence` and
`OrdinaryAmbientAlphaUnits` are used through proof-only `import all` imports; their
statements apply to arbitrary exact functors and adjunctions. The geometric hypotheses
of those modules' main public theorems are not assumed or needed here. Likewise,
`SystemPullbackCompositorEvaluation` is used as a generic comparison tool from the
smooth-purity directory; its statement has no purity or geometric finiteness hypothesis.
The blueprint unit has no realized proof steps that this replacement bypasses.

The rework table contains a historical quarantine entry, but the current assigned source
is present. It is restored and proved, with its Lean attachment and statement preserved;
no archived file is withdrawn and no deletion packet is supplied.

## Second reading by Y8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
