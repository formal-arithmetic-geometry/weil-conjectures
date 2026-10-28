## What changed

Proved `AlgebraicGeometry.Proj.exists_twistPullback_fraction_presentation` without
changing its statement. All Lean changes are confined to the assigned module.
Four proved private helpers implement shifted-fraction membership, the surjective
fraction-to-section map with its coefficient law, the balanced tensor presentation,
and generation of the target chart ring by coefficient sections over the source
chart ring. The final proof composes that presentation with the existing affine
pullback comparison and uses its normalized adjunction unit.

The chart-ring generation argument expands homogeneous numerators using `hgraded`.
It needs only surjectivity, so it avoids constructing a full chart-ring scalar
extension isomorphism. Quasi-coherence uses the existing
`AlgebraicGeometry.Proj.isQuasicoherent_twist` statement. The source fraction map is
chosen only from pointwise prescribed sections: their values uniquely determine
those sections. There is no arbitrary choice of undetermined data.

## Proved and sorry left

Closed the single hole in
`AlgebraicGeometry.Proj.exists_twistPullback_fraction_presentation`
(node `lem-sfb-proj-twist-pullback-fraction-presentation`). Added zero holes and
zero split-off statements. No `sorry` remains in the delivered module. The proof
uses existing library statements, including the still-open quasi-coherence result;
this does not claim that the entire imported dependency closure is sorry-free.

## No longer needed

Removed the proof imports
`WeilConjectures.AlgebraicGeometry.ProjGradedModuleSheafExists`,
`WeilConjectures.AlgebraicGeometry.ProjTwistBasicOpenFractions`, and
`Sheaf.RingTheory.HomogeneousLocalizationScalarExtension`.

The node no longer directly uses
`lem-weil-pbc-proj-graded-module-sheaf-exists` or
`lem-sc-proj-single-twist-basic-open-fractions`: the existing quasi-coherence
statement covers the former geometric step, and fraction realization/descent
supply exactly the pointwise formulas used here. These two nodes are still
transitive prerequisites of quasi-coherence and are not withdrawn.

`lem-nagata-homogeneous-localization-scalar-extension` is unnecessary for this
presentation: coefficient-span generation suffices for surjectivity. No module
is withdrawn, and no assertion is made that other consumers no longer need it.

## Where the brief, the DAG or earlier work was wrong

The existing node's plan was mathematically valid but stronger than necessary:
it asked for a chart-ring isomorphism and a fresh quasi-coherent identification.
The library already states quasi-coherence of the concrete twist. Direct
coefficient-span generation replaces the isomorphism calculation. The updated
node records the actual proof dependencies. No statement repair, unit-route
change, shared-definition change, or forced adaptation is needed.

The source section map handles negative shifts explicitly, and the empty-chart
case uses homogeneous-prime localization detection rather than assuming a
nonzero denominator. The ring-span and tensor arguments use neither flatness
nor cancellation.

Validation: the complete module compiled through `lcompile.py` with exit code 0,
no warnings, and a reported time of 34.6 seconds. The original theorem statement
was compared verbatim with the delivered statement and is unchanged. No public
imports or declarations were removed, and all four new helpers are private.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 INFRA.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.ProjTwistPullbackFractionPresentation": "56be1e4073a0a9fc50ff610a253a842dac7c6f2b"}, "results": {"Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistChartInjective": {"hash": "46c8255d072fdca20f087d7492e77d8c74072eda", "status": "INFRA"}}, "seconds": 105, "time": "2026-10-28T14:13:38+0800", "transitive": 0, "version": 1}
```

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
