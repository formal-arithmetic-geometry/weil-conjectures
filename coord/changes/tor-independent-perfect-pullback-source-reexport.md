# AlgebraicGeometry.torIndependent_perfect_pullback_comparison

## Reason

Return C-f37bb required rebasing the passed packet after the item path changed
on `sheaf-dag`. Rechecked the current source and the quarantine row: the live
Sheaf path is absent, the archived module still has the collision below, and the
adopted source theorem is still complete. This packet restores the module from
that current state and is recompiled before a fresh delivery. The quarantine
archive and the source library remain untouched.

Restore the quarantined Sheaf module after upstream sync 5f7b33eac. The original
file fails at its imports: the Sheaf stalk coordinates load
`Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel`, whereas the algebraic
comparison imports the source copy. Both define
`ModuleCat.BaseDerivedTensorCohomologyModel._sizeOf_inst` and cannot coexist.

The adopted source module already supplies the complete proof of this theorem,
including its private stalk-cohomology identification. Restore the old module path
as a compatibility import of that source module, and point the theorem's DAG
attachment at its actual defining module. No source-library file is modified.

## Old

The quarantined module publicly imports
`WeilConjectures.AlgebraicGeometry.PerfectComplex` and
`Sheaf.AlgebraicGeometry.PullbackStalkTensorComparison`, and defines:

```lean
theorem torIndependent_perfect_pullback_comparison
    {X S T : Scheme.{u₁}} (f : X ⟶ S) (g : T ⟶ S)
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w₁} (SheafOfModules.{u₁} ((moduleRings X.toRingedSpace).over U))]
    [HasDerivedCategory.{w₁}
      (SheafOfModules.{u₁} (moduleRings (Limits.pullback f g).toRingedSpace))]
    (hTor : PullbackStalkTensor.IsTorIndependent f g)
    (P : schemeDerivedCategory X) (hP : Scheme.IsPerfect X P) :
    ∀ z : ↥(Limits.pullback f g), PullbackStalkTensor.IsComparisonIso f g P z
```

It additionally contains two proved private helpers, `stalk_additive` and
`kFlat_pullback_stalk_cohomology`, and no `sorry`.

## New

```lean
module

public import WeilConjectures.AlgebraicGeometry.TorIndependentPerfectPullbackComparison
```

The public theorem is supplied by that import with the exact signature above,
including every universe, derived-category instance, Tor-independence hypothesis,
and perfectness hypothesis. Both coordinate implementations use the actual scheme
stalk rings and the explicit tensor-product lift of the projection stalk maps.
Both derived pullback implementations are the left-derived tensor pullback with
the K-flat counit; the source calls the same K-flat condition `IsKFlatTensor`
where the Sheaf version calls it `IsAcyclicTensorKFlat`. No mathematical assertion
is strengthened or weakened. The upstream proof follows the recorded three-step
K-flat route and has no local proof holes.

The exported implementation of the stalk coordinates and derived pullback now
comes consistently from the source library. This is an interface change, so the
packet requires independent review. No target statement is edited. Any subsequent
target-statement audit should use these source definitions; they represent the
same canonical comparison and the same left-derived pullback.

## Users

The required `tools/downstream.py --allow-missing --uses` scan reports zero
downstream modules and zero declaration users. No live or quarantined Lean module
imports the old Sheaf item path. The actual
consumer already imports the source counterpart. A textual scan of `lean/` and
`quarantine/` finds the following declaration user:

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.AlgebraicGeometry.TorIndependentPerfectTensorBaseChange | unclaimed | Already imports the source theorem; unchanged. |
| Sheaf.AlgebraicGeometry.TorIndependentPerfectPullbackComparison | T5 | Restore as a compatibility import; no duplicate declarations. |

The node `lem-pc-tor-independent-perfect-tensor-base-change` cites this node and
continues to use exactly its original mathematical assertion. No consumer needs
adaptation, and no source-library declaration, signature, attribute or import is
changed.

## Status

landed 20261020T150707-L-2574801 2026-10-20 (merge of deliver/T5/Sheaf.AlgebraicGeometry.TorIndependentPerfectPullbackComparison)
