## What changed

Replaced the proof of `AlgebraicGeometry.Proj.scalarExtension_twistMap_chart_injective`
without changing its signature or public imports. It now compares pullback sections with
coefficient tensors of actual homogeneous fractions. Tensor induction proves that the
prescribed pointwise formula for η agrees with the localized algebra map, and homogeneous
prime localization detection gives injectivity.

Added `Sheaf.AlgebraicGeometry.ProjTwistFractionTensor`: a concrete span of degree-j
fractions, a common-denominator representative theorem, and an injective S-linear map
from its scalar extension into B localized at ψ(f). Its proof uses the direct-sum grading
and the ordinary localization zero criterion; it assumes neither flatness nor faithful
scalar extension.

Added `Sheaf.AlgebraicGeometry.ProjTwistPullbackFractionPresentation` for the remaining
geometric presentation. This is a surjective presentation with an explicit normalization
on pure tensors. It has no η, kernel assertion, or injectivity conclusion. Updated the
item node's proof route and recorded both new nodes. No existing definition or statement
was changed, and no source-library file was changed.

Validation: all three delivered modules compiled through lcompile.py in import order.
The original item compiled in 10.2 seconds; the proved algebra module compiled in
8.5 seconds on its first successful check. There are no compiler errors or non-sorry
warnings. The original theorem signature was checked verbatim against the shared source,
and the new theorem signatures match their DAG records.

## Proved and sorry left

Closed the original body of
`AlgebraicGeometry.Proj.scalarExtension_twistMap_chart_injective` (1 original hole),
conditionally on the named geometric presentation below. Added 1 hole, so this is a
decomposition with net 0 holes closed, not a completed proof of the entire dependency
closure.

The following added declarations have complete proofs and no sorry:
`AlgebraicGeometry.Proj.twistChartFraction_representative` and
`AlgebraicGeometry.Proj.exists_twistChartFraction_tensor_embedding`
(node `lem-sfb-proj-twist-fraction-tensor`). The fraction submodule is an explicit span,
not data chosen from an unproved existence theorem.

The only sorry remaining in this delivery is
`AlgebraicGeometry.Proj.exists_twistPullback_fraction_presentation`
(node `lem-sfb-proj-twist-pullback-fraction-presentation`). Its docstring gives the full
standard-open argument and handles arbitrary integer twists and nilpotent f.
The original item module contains zero sorry.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.RingTheory.HomogeneousLocalizationScalarExtension`
- `Sheaf.Algebra.Module.GradedLocalizationScalarExtension`
- `WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections`
- `WeilConjectures.AlgebraicGeometry.ProjGradedModuleSheafExists`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`
- `WeilConjectures.AlgebraicGeometry.ProjTwistBasicOpenFractions`

The geometric presentation retains the homogeneous-localization, affine-section,
graded-sheaf, and single-twist fraction dependencies. They are not globally pruned.
`lem-sfb-graded-module-localization-scalar-extension` and its module
`Sheaf.Algebra.Module.GradedLocalizationScalarExtension` are unnecessary for this branch:
the new algebraic proof uses common denominators and Mathlib's injectivity of base-changed
graded-piece inclusions directly. The generic tilde proof import is also unnecessary here.
No module is withdrawn, and no blueprint unit or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original proof plan does not expose the normalized comparison between sections of
the actual locally-fraction twist's pullback and the tensor of its homogeneous fractions.
The single-twist chart and associated-graded-sheaf declarations need an identification
on the standard-open basis before the affine pullback comparison applies. This is the
strict geometric step left in the new presentation theorem. The algebraic injection and
the pointwise comparison with η are now separate complete Lean arguments.

Detecting a source section after scalar extension would require unwarranted faithfulness.
The proof instead detects the coefficient tensor, using the direct-sum decomposition of
the graded algebra. It uses no cancellation of f or flatness hypothesis. Edge cases
include negative j, noninjective R→S, zero rings, and nilpotent f; common denominators and
the localization zero criterion apply in all of them.

## New nodes

`lem-sfb-proj-twist-fraction-tensor` records the concrete homogeneous fraction piece,
its single-fraction representatives, and the proved normalized tensor embedding. Its
module contains no holes.

`lem-sfb-proj-twist-pullback-fraction-presentation` records only the geometric surjective
presentation of pullback sections and its pure-tensor normalization. This is strictly a
part of the original argument: it asserts neither injectivity nor the original conclusion,
and the main module supplies the independent algebraic and η comparison arguments.

No change record is needed: existing signatures, definitions, attributes and public
imports are unchanged.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistChartInjective": "46c8255d072fdca20f087d7492e77d8c74072eda", "Sheaf.AlgebraicGeometry.ProjTwistFractionTensor": "d3d8c79e984230911d5037e75711cd70baa8d903", "Sheaf.AlgebraicGeometry.ProjTwistPullbackFractionPresentation": "97e2a5df9df8ff3886a3d1ed9f8d70184f8d4891"}, "results": {"Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistChartBasic": {"hash": "5037cd18cc8644b6c787b9c150b645dfc264b7ef", "status": "OK"}}, "seconds": 69, "time": "2026-10-28T12:20:44+0800", "transitive": 0, "version": 1}
```

## Second reading by Z8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
