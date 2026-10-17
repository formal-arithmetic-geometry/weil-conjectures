## What changed

Proved `integralResidue_tensorPullCounit_core` by the categorical normalization
in its original plan. The generic calculation moves the coefficient counit
through inverse braiding and the tensor product, uses presentation naturality,
and applies the defining balanced tensor counit equation. The concrete proof
uses the named residue pullback and counit. The existing intermediate statement
names its original balanced-counit let body instead of rebuilding it. That name unfolds to exactly the original term; a
reflexivity proof of equality compiled. Unused SX, φX and monoidal-instance lets
are removed by let reduction. All outer binders and the mathematical equality
are unchanged. The change record gives both statement presentations.

Three construction modules expose fully proved equations for those actual maps:
`IntegralResidueTensorPresentation`, `IntegralResidueTensorModel`, and
`IntegralResidueTensorPullPresentation`. The single-object comparison and derived
braiding have stable names. The paper tensor presentation uses the named balanced
counit, whose left-derived property is proved. The generic tensor model accepts a named derived functor and counit. The paper
model keeps its original constructor. The kernel checks its definitional equality
with the named pullback specialization. No object is selected from an unproved existence theorem.

These definition/API changes address measured 60-second conversion failures:
unfolding the concrete derived-functor implementation and repeatedly comparing
monoidal dictionaries was expensive. The generic categorical calculation compiles
quickly. The final specialization takes its category parameters from the actual tensor
presentation constructor on X and Y. The first four specify the base category,
category instance, abelian instance and Grothendieck instance; the first nine
also specify the monoidal, closed, preadditive, braided and flat-resolution
instances. The generic theorem application is assigned directly and Lean's kernel
checks it against the public statement. The emitted module compiled in 48.1
seconds and a separate module imported it successfully. The construction modules
compiled in 26.2, 22.1 and 39.0 seconds. The parent retains its statement and
unfolds the named counit in its final proof step.

All seven checked consumers compile against the emitted modules: the parent
`IntegralResidueTensorPullCounitModel` (42.6 seconds),
`IntegralResidueScalarGeometryBridge` (57.5), `IntegralResidueScalarRouteModel` (43.4),
`IntegralResidueTensorGeometry` (50.4), `IntegralResidueTensorSquare` (41.5),
`IntegralResidueScalarCounitModel` (55.9), and `IntegralResidueTensorRouteModel` (26.4).
Only the parent needs a proof adaptation: unfold the named counit and reduce
identity wrappers. Its signature and visibility stay identical.
The final five-module delivery dry run passed compilation and preflight (`OK`),
with review class CODEX for the recorded construction/API and node changes.

Change records describe the final constructors, equivalent intermediate statement,
consumer checks and the affected target-definition review:
`coord/changes/A3-residue-presentation-defining-equations.md`,
`coord/changes/A3-tensor-model-derived-braiding-name.md`, and
`coord/changes/A3-core-named-counit-statement.md`.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_tensorPullCounit_core`
(node `new-integral-residue-tensor-pull-counit-core`), 1 of 1 original holes.
Added: 0 holes. Split off: 0. Remaining holes in the item: 0.
An importing axiom probe reports exactly `propext`, `Classical.choice`, and
`Quot.sound` for the closed core theorem (2.1 seconds).
All added construction equations and compatibility proofs are proved. No definition
contains sorry. The earlier attempt's draft modules `IntegralResidueTensorPullModelFactor` and
`IntegralResidueTensorPullPresentationFactor` are excluded. Their unpublished
nodes `new-integral-residue-tensor-pull-model-factor` and
`new-integral-residue-tensor-pull-presentation-factor` are unnecessary; neither
is an imported dependency or a new obligation.

## No longer needed

Removed the core's public import of `IntegralResidueScalarCounitModel` and its
proof-dependency edge `new-integral-residue-scalar-counit-model`: the tensor middle
normalization uses only the coefficient comparison and balanced tensor equations.
The parent independently imports the scalar module, so no whole module is claimed
pruned. Removed redundant direct proof imports of `IntegralReductionTensor` and
`IntegralResidueTensorPresentation`, already public through the pull presentation.
The core's old private coefficient-counit helper is now the proved construction API
`Functor.tensorModelCoefficientIso_counit`; the generic tensor normalization remains
in the core. Unused experimental lemmas `residueExchangeTensorIso_def` and
`residueExchangeTensorModelTarget_with`, and the homotopy-comparison cache,
are excluded. No protected blueprint unit statement
or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was found false. A single-file lcompile check does not
write its module to .lbuild; the multi-file form does. Consumer verification uses
the multi-file form to avoid loading the published, still-holed core artifact. The retained attempt decomposed the
core despite already having the essential generic argument. Its remaining issue
was concrete instance conversion. This delivery follows the original tensor
calculation and closes that chain without new holes. All steps use isomorphism
cancellation and naturality, so zero coefficients, zero complexes, empty schemes,
and identity pullbacks require no extra nonvanishing assumptions.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
