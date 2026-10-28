## What changed

Replaced the sorry in
`AlgebraicGeometry.Proj.scalarExtension_twistMap_chart_surjective` with a direct
homogeneous-fraction proof. Fraction descent gives a target numerator and a power
of the chart denominator. The grading hypothesis expresses the numerator in the
S-span of images of source homogeneous elements. Span induction lifts generators
using fraction realization and the prescribed pointwise formula, lifts sums
additively, and lifts scalar multiples using degree-zero regular chart sections
and O-linearity. Empty charts and negative shifted numerator degrees are handled
explicitly. The declaration's signature and public imports are unchanged.

Updated the assigned node's proof, proof dependencies and proof origin to match
this argument. Only the assigned Lean module and its own node change.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Proj.scalarExtension_twistMap_chart_surjective`
(node `lem-sfb-proj-scalar-extension-twist-chart-surjective`).
No sorry remains in the module. No holes were added or split off. The proof uses
the existing fraction descent and realization declarations. The single-file
compiler accepted the complete proof in 9 seconds; delivery also runs the
required declaration/axiom probe and preflight checks.

## No longer needed

Removed these proof-only imports and their corresponding planned dependencies:

- `Sheaf.RingTheory.HomogeneousLocalizationScalarExtension`
  (`lem-nagata-homogeneous-localization-scalar-extension`).
- `Sheaf.Algebra.Module.GradedLocalizationScalarExtension`
  (`lem-sfb-graded-module-localization-scalar-extension`).
- `WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections`
  (`lem-weil-pbc-module-pullback-affine-sections`).
- `WeilConjectures.AlgebraicGeometry.ProjGradedModuleSheafExists`
  (`lem-weil-pbc-proj-graded-module-sheaf-exists`).
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`.
- `WeilConjectures.AlgebraicGeometry.ProjTwistBasicOpenFractions`
  (`lem-sc-proj-single-twist-basic-open-fractions`).

The last module is replaced by direct proof imports of
`WeilConjectures.AlgebraicGeometry.ProjTwistFractionDescent` and
`WeilConjectures.AlgebraicGeometry.ProjTwistFractionRealization`.
These removals prune this theorem's route only: the other chart component still
lists the earlier dependencies, and no global unreachability is claimed. No
source-library declarations or modules are removed. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned chain of affine tensor-section and localization equivalences is
unnecessary for surjectivity. The explicit hypothesis `hgraded` already supplies
all target homogeneous numerators as scalar combinations of source numerators;
`hη` computes the image of their realized fractions. Neither the tensor
presentation equivalence `β` nor its compatibility hypothesis is needed in this
half of the chart argument, but both remain in the unchanged signature.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistChartSurjective": "b38740735a11488f8f5284668ee32f502f4b90bc"}, "results": {"Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistChartBasic": {"hash": "5037cd18cc8644b6c787b9c150b645dfc264b7ef", "status": "OK"}}, "seconds": 81, "time": "2026-10-28T12:03:19+0800", "transitive": 0, "version": 1}
```

## Second reading by Z9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
