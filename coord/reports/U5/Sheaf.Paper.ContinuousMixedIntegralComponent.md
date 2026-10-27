## What changed

`Sheaf.Paper.ContinuousMixedIntegralComponent` now constructs its arrow by applying the actual
rationalization functor to the restricted published `pbcScalarCompletedPullIso` component. Its
heterogeneous normalization is reflexive, using the literal raw object formulas.

The complete comparison argument solves the supplied `Along.completion_unit` and
`FieldChange.integral_normalization` equations, proves naturality of the pair of scalar tensor
associators, and uses naturality of the integral realization. Postcomposition by a specified
isomorphism reduces the desired equation to the ordinary mixed tensor cube. The existing
`scalarCompletedPull_unit` equation then replaces the ordinary scalar comparison and E unit
by the F unit and the published completed component. The F normalization cancels the remaining
comparison. In particular, completion-unit cancellation and the actual choice of the raw arrow
are implemented here, rather than deferred again.

The new module `Sheaf.Paper.ContinuousMixedOrdinaryBalance` constructs
`FieldChange.integralBalance` from the two specified `pbcReductionNormalization` isomorphisms
and states the remaining cube before completion. Its input is an arbitrary ambient integral
derived object. Its equation contains neither raw rationalization, realization functors or
comparisons, nor completion units. It is strictly the ordinary balancing step of the original
argument, not the original conclusion with renamed or repackaged hypotheses.

The existing item signature and public imports are unchanged. Only the item, this new module,
and their DAG records are changed. No shared definition, other existing module, or upstream
source declaration is changed.

Validation: both sandbox modules passed the required remote `lcompile.py` checks. The final
assigned module compiled in 14.3 seconds with no profiling options. Its signature was compared
with the repository source and is unchanged; both JSON records parse and Lean lines are at
most 100 characters. Delivery preflight supplies the independent compiler and axiom checks.

## Proved and sorry left

Closed upper hole:
`AlgebraicGeometry.Scheme.ContinuousRational.continuousMixedIntegralComponent`
(`lem-per-continuous-mixed-integral-component`). Its proof is complete from the named ordinary
cube and existing declarations.

Added lower hole:
`AlgebraicGeometry.Scheme.ContinuousRational.continuousMixedOrdinaryBalance`
(`lem-per-continuous-mixed-ordinary-balance`). This is the only remaining `sorry` in the packet;
it is the entire proof of a public named theorem in its own module.

This delivery is a decomposition: one upper hole closed, one strictly simpler lower hole added,
net zero holes. It does not claim an unconditional proof of the whole mixed comparison.
`FieldChange.integralBalance` is a real composite of existing canonical isomorphisms, with no
postponed data. All private helper theorems in the item have complete proofs.

The ordinary equation makes sense for zero inputs, empty schemes, identity scheme maps,
identity field embeddings and repeated fields. No inverse completion unit on an arbitrary
ambient object is asserted: the canceled postcomposition is explicitly the image of the
composite of the supplied comparison inverse and integral comparison.

## No longer needed

No existing import is removed, and no module is withdrawn. The existing public import of
`ContinuousAmbientMixedCoherence` remains necessary for `AmbientMixed`.

The broad original proof-plan inputs `lem-per-rational-realization-scalar-coherence`,
`prop-weil-pbc-scalar-extension` and `lem-weil-pbc-constant-completion-equivalence` are not used
as direct proof inputs. In particular the proof adds no import of
`RationalRealizationScalarCoherence` or `ConstantCompletionEquivalence`. It uses the precise
already-proved completion-unit equation from `PbcScalarAmbientOperations`, and scalar
normalization naturality from `CompletedPullbackReductionCoherence`, instead. Definitions
already re-exported through the unchanged public imports remain available and needed; this
is not a claim that the corresponding entire modules leave the targets' closure.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The original proof plan combines the
ordinary balancing cube and completion-unit cancellation in prose; these are distinct steps.
The latter is now a full Lean calculation. The former needs a compatibility equation between
the independently normalized integral and rational ordinary comparisons; none of the listed
existence records states that equation. Existing generic tensor and derived-adjoint APIs are
proof tools, but their model interfaces do not directly identify this particular cube.

## New nodes

`lem-per-continuous-mixed-ordinary-balance`, in `dag/nodes/sec-deligne-laumon-a1/`, records the
ambient ordinary cube with its exact Lean attachment, source, generator proof and descent
plan. The source is BS Remark 6.8.15, p. 62, and Stacks Tag 0D6D,
`sites-cohomology.tex`, `lemma-derived-pullback-composition`. Its two tensor associators are
constructed explicitly. The blueprint search for "mixed balancing" returned no existing
blueprint statement. The parent node now records the explicit unit-cancellation proof and
this strictly smaller dependency. The unit's realized statement and steps are preserved.

## Second reading by U5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
