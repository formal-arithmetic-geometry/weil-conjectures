# Sheaf.Paper.FiniteCoefficientReductionFlatModel

## Reason

Restore the module quarantined by the 2026-10-23 cluster-restore build. The archived
module has zero holes but exceeds the 60-second single-file compile limit. Diagnostic
prefixes locate the expensive conversion inside `proEtale_torAmplitude_of_flatModel`:
the original proof through the termwise homology calculation compiles in 12.9 seconds,
but adding the total/termwise comparison exceeds the limit. The comparison mixes the
named ordinary-tensor API with the unfolded `curriedTensor`. Use the same named tensor
throughout and identify the native tensor by the published tensor equality explicitly.
All original public signatures, definition bodies, imports and docstrings are preserved.
Only private proofs and local proof-elaboration commands change. The next full compile
with the earlier abstraction reached the etale proof in 54.3 seconds but exhausted the
default instance-search budget on `T.smallEtaleTopology.W.IsMonoidal`. Supplying Mathlib's
named monoidality instance replaces that search. The new tensor instances are confined
to the private pro-etale helper's section.

## Old

```lean
  let F := tensorRight M
```

```lean
    DerivedCategory.Q.mapIso (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor C) M P') ≪≫
```

```lean
  exact ht.of_iso ((DerivedCategory.homologyFunctor C i).mapIso eq)
```

The three named tensor API facts were not registered as local instances in this file.
The existing irreducibility attributes for `flatModelReductionData` and
`flatModelReductionDerivedData` occurred only after their downstream definitions and
`chosenCounit_modelIso`.

```lean
  have : (T.smallEtaleTopology.W (A := ModuleCat.{u + 1} R)).IsMonoidal := inferInstance
```

## New

```lean
section

attribute [local instance] SheafOfModules.KFlatFixedTensor.tensorAdditive
  SheafOfModules.KFlatFixedTensor.tensorObjAdditive
  SheafOfModules.KFlatFixedTensor.tensorHasMapBifunctor
```

```lean
  let F := (SheafOfModules.KFlatFixedTensor.ordinaryTensor R).flip.obj M
```

```lean
    DerivedCategory.Q.mapIso (CochainComplex.mapBifunctorSingle₂Iso
      (SheafOfModules.KFlatFixedTensor.ordinaryTensor R) M P') ≪≫
```

```lean
  have heq : derivedTensor T A L S₀ P' f hf hP' = DerivedCategory.Q.obj
      (((SheafOfModules.KFlatFixedTensor.totalTensor R).obj P').obj S₀) := by
    simp only [SheafOfModules.KFlatFixedTensor.totalTensor,
      SheafOfModules.KFlatFixedTensor.ordinaryTensor_eq_published]
    rfl
  exact ht.of_iso ((DerivedCategory.homologyFunctor C i).mapIso (eqToIso heq ≪≫ eq))
```

The helper's section ends before the public coefficient-level declarations. The two
existing data-abstraction attributes now occur immediately after their definitions:

```lean
attribute [local irreducible] flatModelReductionData
```

```lean
attribute [local irreducible] flatModelReductionDerivedData
```

The etale proof now supplies the existing Mathlib instance directly:

```lean
  have : (T.smallEtaleTopology.W (A := ModuleCat.{u + 1} R)).IsMonoidal :=
    GrothendieckTopology.W.monoidal (J := T.smallEtaleTopology) (A := ModuleCat.{u + 1} R)
```

The private counit computation additionally supplies the exact additive witness of the
selected functor and applies the generic helper to that raw selected functor:

```lean
  let : (flatModelReductionData l E m n hmn T).choose.Additive :=
    (flatModelReductionData l E m n hmn T).choose_spec.choose_spec.choose_spec.choose
  exact chosenCounit_modelIso (flatModelReductionData l E m n hmn T).choose
    (fun P ↦ P.IsKFlatIndependentCoefficients)
    (flatModelReductionDerivedData l E m n hmn T) P hk
```

This uses the same witness as `flatModelReductionChange_additive`; no new ordinary or
derived functor is selected. A diagnostic with the raw functor and no explicit witness
reported `failed to synthesize ...choose.Additive` after 49.9 seconds. The original
named-wrapper application spends 16–22 seconds on the `exact` tactic in profiling.

The private `chosenCounit_modelIso` helper now takes the universal-counit property
explicitly instead of inferring an arbitrary predicate `r LF ε`. Its conclusion and
three-arrow proof are unchanged. The new property parameter is:

```lean
    (F : C ⥤ D) [F.Additive] (KF : CochainComplex C ℤ → Prop)
    (H : ∃ (LF : DerivedCategory C ⥤ DerivedCategory D)
      (ε : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh),
      LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ)) ∧
        (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
        ∀ P, KF P → IsIso (ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj P)))
    (P : CochainComplex C ℤ) (hk : KF P)
```

Its old predicate inputs were:

```lean
    (F : C ⥤ D) [F.Additive]
    (r : ∀ (LF : DerivedCategory C ⥤ DerivedCategory D),
      (DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) → Prop)
    (H : ∃ LF ε, r LF ε) (P : CochainComplex C ℤ)
    (h : ∀ LF ε, r LF ε →
      IsIso (ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj P)))
```

No private helper appears in a public signature or definition body.

## Users

`tools/downstream.py Sheaf.Paper.FiniteCoefficientReductionFlatModel --allow-missing
--direct --names` returns no current library consumers because the restoration cluster
is quarantined. A source search additionally finds the following archived direct
consumers. All public declarations and definition bodies are restored unchanged, so no
consumer statements change and no consumer adaptation is needed. The local instance
attributes are not exported. No target signature or definition used by a target changes.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.EtaleFiniteCoefficientHomArrow` | unclaimed in shared claim snapshot | Quarantined; unchanged API, no adaptation. |
| `Sheaf.Paper.EtaleLocallyClosedShriek` | unclaimed in shared claim snapshot | Quarantined; unchanged API, no adaptation. |
| `Sheaf.Paper.ExplicitExceptionalPreservation` | unclaimed in shared claim snapshot | Quarantined; unchanged API, no adaptation. |
| `Sheaf.Paper.FiniteEtaleDescent` | unclaimed in shared claim snapshot | Quarantined; unchanged API, no adaptation. |
| `Sheaf.Paper.FiniteFirstRootChart` | unclaimed in shared claim snapshot | Quarantined; unchanged API, no adaptation. |
| `Sheaf.Paper.FinitePositiveRootCharts` | unclaimed in shared claim snapshot | Quarantined; unchanged API, no adaptation. |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed in shared claim snapshot | Quarantined; unchanged API, no adaptation. |
| `Sheaf.Paper.FiniteRootTensorPresentation` | unclaimed in shared claim snapshot | Quarantined; unchanged API, no adaptation. |
| `Sheaf.Paper.FiniteSignedTwistProducts` | unclaimed in shared claim snapshot | Quarantined; unchanged API, no adaptation. |
| `Sheaf.Paper.FiniteTensorFixedComparisons` | unclaimed in shared claim snapshot | Quarantined; unchanged API, no adaptation. |
| `Sheaf.Paper.FiniteTensorPresentationReduction` | unclaimed in shared claim snapshot | Quarantined; unchanged API, no adaptation. |
| `Sheaf.Paper.FiniteTensorSignedReduction` | unclaimed in shared claim snapshot | Quarantined; unchanged API, no adaptation. |
| `Sheaf.Paper.FrobeniusCoefficientReductionMap` | unclaimed in shared claim snapshot | Quarantined; unchanged API, no adaptation. |
| `Sheaf.SixFunctors.CompactCoefficientComposition` | unclaimed in shared claim snapshot | Quarantined; unchanged API, no adaptation. |
| `Sheaf.SixFunctors.FiniteExceptional` | unclaimed in shared claim snapshot | Quarantined; unchanged API, no adaptation. |

## Status

landed 20261023T231553-L-3618561 2026-10-23 (merge of deliver/J1/Sheaf.Paper.FiniteCoefficientReductionFlatModel)

An intermediate complete restoration compiled cleanly in 35.3 seconds, but its delivery
compile timed out under the same 60-second bound. The explicit additive witness above
addresses the subsequent diagnostic. Zero holes remain; no holes or new statements were
added. Final validation is recorded in the report.
