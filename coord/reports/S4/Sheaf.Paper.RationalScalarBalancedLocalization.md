## What changed

In `Sheaf.Paper.RationalScalarBalancedLocalization`, proved
`AlgebraicGeometry.Scheme.rationalBalancedIntegralNormalization` from the specified finite
normalizations and the injective profinite-tower presentation of the coefficient integers.
Moved the existing private finite-chart helpers before this theorem and added one proved
private finite scalar-chart helper. Added the proof-only import
`Sheaf.NumberTheory.Padics.IntegersProfiniteTower`. Added the proof-only import
`Sheaf.Paper.CompletedPullbackReductionCoherence` for the proved normalized tensor
associativity helper. The pentagon follows by tensoring its integral equation with one,
using the pure-tensor formulas for raw coefficient extension and composition, then
applying realization. Disabled `ULift.module` only while elaborating this one proof to
select the existing localization module action. All public signatures, constructions,
attributes and imports are preserved. Updated the owning node's proof and dependencies.
The sectionwise argument covers ramified embeddings and empty test objects.

The restored item initially compiled in 72.9 seconds and failed the 60-second gate.
The final identity-transport proof now uses proved private category-theoretic cancellation
and indexed equality-transport lemmas, avoiding expansion of the concrete coefficient
functors. The full delivered module compiled in 42.6 seconds, below the 60-second limit.

## Proved and sorry left

Closed 2 of the 6 original holes, with no holes added:
`AlgebraicGeometry.Scheme.rationalBalancedIntegralNormalization` and
`AlgebraicGeometry.Scheme.rationalBalancedPentagon`.

Four existing holes remain, all owned by
`lem-per-rational-scalar-balanced-localization`:

- `AlgebraicGeometry.Scheme.rationalBalancedComponent_naturality`
- `AlgebraicGeometry.Scheme.rationalBalancedTensorModels`
- `AlgebraicGeometry.Scheme.rationalBalancedTower`
- `AlgebraicGeometry.Scheme.rationalBalancedIdentity`

## No longer needed

None. No public import, node, module or unit-route dependency is pruned.

## Where the brief, the DAG or earlier work was wrong

The stale build-error record reports a bad import of
`Sheaf.Paper.RationalModuleRealizationFunctor`; the shared snapshot now restores that
module and this item. The restored item nevertheless exceeded the single-file time gate.
The new proof is substantive and does not count restoration or recompilation as proof.
The original finite-projection argument also needs injectivity of the integral
profinite-tower presentation; the DAG now cites its existing owner explicitly.

## Related modules compiled before delivery

Not checked: the delivered modules did not compile in the overlay (service fault); the landing compiles the related modules.

```json
{"capped": false, "direct": 3, "left_out": 0, "own": {"Sheaf.Paper.RationalScalarBalancedLocalization": "3c1d3f7192b3f254a63bc736ddc70b634648f9f2"}, "own_failed": ["Sheaf.Paper.RationalScalarBalancedLocalization"], "results": {}, "time": "2026-10-28T00:59:55+0800", "transitive": 0, "version": 1}
```

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
