## What changed

Implemented `AlgebraicGeometry.Scheme.ContinuousRational.rationalContinuousPullbackTransport`
without changing its statement or any existing public definition. All edits are confined to
the item, its node, and one new ordinary-pullback module and node.

The proof now establishes the completed part of the argument in Lean. It obtains strict
completed membership and invertibility of the specified strict unit from
`rationalRealizationPullbackComparison`, transfers them through the augmentation-normalized
`pbcActualCompletedPullback_tower`, and uses isomorphism closure of the integral predicate.
It constructs the integral comparison from the given realization isomorphisms, the inverse
completion unit and ordinary ambient balance. `ScalarLocalization.naturalIso_of_integral`
extends this comparison to every raw rational arrow. The component equation and inverse
identities prove precisely `completion_unit`. This argument needs no target linearity.

Pointwise extensionality after the sheaf adjunction proves uniqueness of normalized coefficient
maps. The existing slice-normalization theorem then proves coefficient invertibility and
ordinary exactness for etale maps and immersions. The final constructor assembles these
proved clauses with the ordinary data.

The smaller remaining theorem `rationalContinuousOrdinaryPullback` concerns coefficient,
ordinary tensor and universal derived-counit normalization. Its record depends only on the
two completed-to-rational coefficient homomorphisms. It contains neither completed membership,
raw rational functors, realization comparison, completion-unit equation, nor the special
exactness clause. This is the ordinary step of the existing plan, not a renamed `Along`
existence theorem. Its docstring and new node give the complete section and K-flat proof plan.

Validation: the server compiler checked both modules during development; its last diagnostic
reduced the completed comparison to functorial preservation of an identity, now discharged
explicitly. The final warning-free compile, axiom checks and required server preflight are
run and recorded by the delivery tool before it pushes this packet. Profiling options
used during development have been removed.

## Proved and sorry left

Closed the one existing hole in
`AlgebraicGeometry.Scheme.ContinuousRational.rationalContinuousPullbackTransport`
(node `lem-per-rational-continuous-pullback-transport`). Its proof from the smaller ordinary
statement and existing declared dependencies is complete.

Added one hole:
`AlgebraicGeometry.Scheme.ContinuousRational.rationalContinuousOrdinaryPullback`
(node `lem-per-rational-continuous-ordinary-pullback`). This is the only `sorry` in the
new module and the only hole added by this delivery. There are zero holes in the item.
This is a decomposition: one hole closed, one strictly smaller hole added, net zero.
No claim is made that the transitive dependencies are free of `sorry`.

The private tensor-with-one comparison, coefficient-uniqueness, special-exactness,
completed-preservation and completed-comparison helpers have complete proofs and
introduce no holes.

## No longer needed

Removed the item's direct proof import
`Sheaf.AlgebraicGeometry.ProEtaleInverseImageScalarUnitNormalization`. Its multiplication
normalization is still part of the ordinary sub-obligation's stated proof plan, so its DAG
node is not withdrawn. The new ordinary module imports only its statement data.

The transport proof does not need the raw comparison's `alpha`, `alpha_normalization`,
`raw_objects` or `raw_fractions` fields. Categorical descent of the comparison assembled
from the actual completion unit replaces transport of those fields. The dependency module
`Sheaf.Paper.RationalRealizationPullbackComparison` remains needed for integral membership
and the specified strict-unit isomorphism; its declarations and node are preserved.

No existing module or DAG node is withdrawn. The unit's statement and proof steps remain
on their existing route.

## Where the brief, the DAG or earlier work was wrong

The original plan asked for extension of an integral comparison by checking all fractional
arrows explicitly. The existing `ScalarLocalization.naturalIso_of_integral` provides this
extension directly, without additivity or linearity assumptions on either target functor.
The parent node now records this shorter categorical step.

The rework row records an old dependency on `SfP1ProjectionTraceFalseTail`. The restored
item source used here already has its original single hole and has no such direct import.
The delivery preserves the source and attachment and replaces the hole by an actual
completed-unit/descent proof; it does not withdraw the quarantined item or introduce any
false-tail theorem.

## New nodes

`lem-per-rational-continuous-ordinary-pullback`, in
`dag/nodes/sec-deligne-laumon-a1/`, realizes the ordinary coefficient, tensor and derived
computation-counit step before completion. Its Lean module is
`Sheaf.Paper.RationalContinuousOrdinaryPullback`. Empty schemes are allowed; no coefficient
isomorphism is assumed for a general morphism, and K-flat computation does not add a
flat-term hypothesis. Flat-term replacements explain this last point in the proof plan.
No existing statement or definition changes and no change record is required.

## Second reading by K8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
