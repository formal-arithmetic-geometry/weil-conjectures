# DerivedRHomAlgebraModule elaboration scopes

## Reason

The saved complete proof repeatedly exceeded the 60-second limit. Generic private helpers
were being elaborated in the scope of concrete derived-category instance binders. Moving
them ahead of the scheme variables and avoiding duplicate ambient binders on the explicitly
bound definition reduces the full compile to about 51 seconds. The checker conservatively
classifies section/variable and local-instance commands as an interface change.
Every existing public declaration keeps its signature and visibility; every definition body
and public import stays identical. No target changes meaning. No downstream adaptation is needed.

## Old

The scheme variables preceded all private helpers. The ambient block
```lean
variable (hB : B.toModule.IsQuasicoherent)
  [HasDerivedCategory.{w} (SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf))]
  [HasDerivedCategory.{wB} (SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat)).obj B.right))]
```
also preceded `derivedRHomAlgebraModule`, which explicitly binds the same instances.
Finite-limit and finite-colimit proofs were concrete proofs in this variable scope.

## New

Generic private helpers precede `variable (Y : Scheme.{u}) (B : Y.CommAlgebraSheaf)`.
A `section` around the existing ambient binders and resolution-inversion theorem ends before
`derivedRHomAlgebraModule`. The same ambient binder block is reopened before
`derivedRHomAlgebraModule_comparison`. Thus no existing signature changes.

The proved private generic scalar-restriction lemmas are registered only locally:
```lean
attribute [local instance] restrictScalars_finite_limits restrictScalars_finite_colimits
```
The final proof and generic comparison helpers locally use the transparency-respecting
elaboration options. These commands do not modify importers' elaboration settings or instances.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineDerivedHomEvaluationCounit | unclaimed | No signature, definition, or visibility change; no adaptation. |
| Sheaf.AlgebraicGeometry.ClosedImmersionExtIdealAction | unclaimed | No signature, definition, or visibility change; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedAlgebraQCohOfUnderlying | unclaimed | No signature, definition, or visibility change; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteAffineDerivedEquivalence | unclaimed | No signature, definition, or visibility change; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteAffineDerivedFactorization | unclaimed | No signature, definition, or visibility change; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteAlgebraHomExact | unclaimed | No signature, definition, or visibility change; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteExactHomDegreeZeroLift | unclaimed | No signature, definition, or visibility change; no adaptation. |
| Sheaf.AlgebraicGeometry.FinitePushforwardDerivedHomQCoherent | unclaimed | No signature, definition, or visibility change; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRestrictionDerivedRightAdjoint | unclaimed | No signature, definition, or visibility change; no adaptation. |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionAlgebraDualHomology | unclaimed | No signature, definition, or visibility change; no adaptation. |
| Sheaf.AlgebraicGeometry.PseudoCoherentRHomQuasiCoherent | unclaimed | No signature, definition, or visibility change; no adaptation. |
| Sheaf.AlgebraicGeometry.SheafAlgebraDerivedHomAdjunction | unclaimed | No signature, definition, or visibility change; no adaptation. |
| Sheaf.AlgebraicGeometry.SheafAlgebraHomAdjunction | unclaimed | No signature, definition, or visibility change; no adaptation. |
| Sheaf.AlgebraicGeometry.SheafAlgebraMapDerivedAdjunction | unclaimed | No signature, definition, or visibility change; no adaptation. |

These are the direct importers. All downstream users see identical public interfaces.

## Status

landed 20261013T100028-L-2468823 2026-10-13 (merge of deliver/M1/Sheaf.AlgebraicGeometry.DerivedRHomAlgebraModule)
