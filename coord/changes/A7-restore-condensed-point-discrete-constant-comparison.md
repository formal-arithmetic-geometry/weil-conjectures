# AlgebraicGeometry.ProEtale.condensed_point_discrete_constant_comparisons

## Reason

The assigned `coord/rework.tsv` row records removal of this module following a reverted
cluster restore. Restore its complete proved archive to the absent live path. This is
missing-source recovery, not a newly closed proof hole.

## Old

The live path `lean/Sheaf/Paper/CondensedPointDiscreteConstantComparison.lean` is absent.
The authoritative source remains at
`quarantine/Sheaf/Paper/CondensedPointDiscreteConstantComparison.lean`.
Its public theorem signature is:

```lean
theorem condensed_point_discrete_constant_comparisons
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (A : Type u) [Ring A] [TopologicalSpace A] [DiscreteTopology A] :
    Nonempty (coefficientRing (Spec (.of Ω))
        (Mon.mk (Profinite.continuousCoefficientRingObj A)) ≅
          (comparisonUpperStar Ab.{u + 1} (Spec (.of Ω))).mapMon.obj
            ((Mon.mk ((sheafCompose (Spec (.of Ω)).smallEtaleTopology
              (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
                ((constantSheaf (Spec (.of Ω)).smallEtaleTopology RingCat.{u + 1}).obj
                  (RingCat.of (ULift.{u + 1} A))))))) ∧
      Nonempty (coefficientRing (Spec (.of Ω))
        (Mon.mk (Profinite.continuousCoefficientRingObj A)) ≅
          (Mon.mk ((sheafCompose (Scheme.ProEt.topology (Spec (.of Ω)))
              (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
                ((constantSheaf (Scheme.ProEt.topology (Spec (.of Ω))) RingCat.{u + 1}).obj
                  (RingCat.of (ULift.{u + 1} A))))))
```

## New

Restore the exact archived source, including its theorem proof, private helpers and all
public and proof imports. The signature above is unchanged. No definitions, mathematical
data, attributes, universes, target statements or target meanings change. No target
semantic review is reopened. The existing DAG attachment and all dependencies are
preserved without edits. The archive itself remains untouched.

## Users

`tools/downstream.py` reports an unknown module because the live source is absent.
An exact search of both `lean/` and `quarantine/` finds the single direct consumer below.
Its unchanged archived source compiles in the sandbox overlay in 5.9 seconds. No consumer
is adapted or included in the delivery. The item itself compiles in 7.1 seconds; its
importing axiom probe reports only `propext`, `Classical.choice`, and `Quot.sound`.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CondensedPointCoefficients | unclaimed | Quarantined consumer; identical restored interface; unchanged source compiles. |

## Status

landed 20261021T020957-L-2685553 2026-10-21 (merge of deliver/A7/Sheaf.Paper.CondensedPointDiscreteConstantComparison)
