# AlgebraicGeometry.ProEtale.condensed_point_coefficients

## Reason

Restore the assigned missing module after the cluster rollback recorded in
`coord/rework.tsv` (2026-10-20). The authoritative archive is
`quarantine/Sheaf/Paper/CondensedPointCoefficients.lean`. Its proofs are complete;
this is source recovery with zero proof holes, not new mathematical progress.

## Old

The live path `lean/Sheaf/Paper/CondensedPointCoefficients.lean` is absent.
The quarantined module has four public constructions:
`condensedPointRingRestriction`, `condensedPointConstantRing`,
`condensedPointFiniteFunctionDiagram`, `condensedPointFiniteFunctionCocone`,
and this public theorem (inside `AlgebraicGeometry.ProEtale`):

```lean
theorem condensed_point_coefficients (Ω : Type u) [Field Ω] [IsSepClosed Ω] :
    (∀ F : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)),
      Nonempty ((profiniteToProEtOf (Spec (.of Ω))).op ⋙
        ((profinitePointSetSchemeInverseImage (Spec (.of Ω))).obj F).obj ≅ F.obj)) ∧
    (∀ F : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}),
      Nonempty ((condensedPointRingRestriction (Spec (.of Ω))).obj
        (coefficientRing (Spec (.of Ω)) F) ≅
          (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMon.obj F)) ∧
    (∀ (T : Type u) [TopologicalSpace T] [Ring T] [IsTopologicalRing T],
      Nonempty ((condensedPointRingRestriction (Spec (.of Ω))).obj
        (coefficientRing (Spec (.of Ω)) (Mon.mk (Profinite.continuousCoefficientRingObj T))) ≅
          (Profinite.continuousCoefficientRingPresheaf T).toMonAb)) ∧
    (∀ (A : Type u) [Ring A] [TopologicalSpace A] [DiscreteTopology A],
      (∀ S : Profinite.{u},
        (∃ e : LocallyConstant S A ≃+* C(S, A), ∀ f : LocallyConstant S A,
          (e f : S → A) = f) ∧
        Nonempty (IsColimit (condensedPointFiniteFunctionCocone A S))) ∧
      Nonempty (coefficientRing (Spec (.of Ω))
        (Mon.mk (Profinite.continuousCoefficientRingObj A)) ≅
          (comparisonUpperStar Ab.{u + 1} (Spec (.of Ω))).mapMon.obj
            (condensedPointConstantRing (Spec (.of Ω)).smallEtaleTopology A)) ∧
      Nonempty (coefficientRing (Spec (.of Ω))
        (Mon.mk (Profinite.continuousCoefficientRingObj A)) ≅
          condensedPointConstantRing (Scheme.ProEt.topology (Spec (.of Ω))) A))
```

## New

Restore the exact archived source at its original live path, including every
construction, proof, attribute, universe and import. The five signatures and their
bodies are identical to the archive. The existing DAG attachment, proof route and
all statement and proof dependencies remain intact. No target statement or
meaning changes, and no target semantic review is reopened. The archive remains
untouched. No other module is adapted.

## Users

`tools/downstream.py Sheaf.Paper.CondensedPointCoefficients --uses
AlgebraicGeometry.ProEtale.condensed_point_coefficients` reports the module as
unknown because its live source is absent. An exact import and declaration-name
search of both `lean/` and `quarantine/` finds no current consumer. The earlier
`FiniteConstantLocalModel` consumer removed this import in its completed proof
(as recorded in its C9 report). This observation does not authorize withdrawing
the assigned quarantined source. Its existing node and unit remain preserved.
The restoration itself compiles cleanly in 8.9 seconds. A further axiom probe
compiles in 5.8 seconds and checks all five public declarations: only `propext`,
`Classical.choice` and `Quot.sound` occur.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CondensedPointCoefficients | B6 (assigned) | Restore exact archived interface and complete proofs; no adaptation. |

## Status

landed 20261021T021905-L-2789669 2026-10-21 (merge of deliver/B6/Sheaf.Paper.CondensedPointCoefficients)
