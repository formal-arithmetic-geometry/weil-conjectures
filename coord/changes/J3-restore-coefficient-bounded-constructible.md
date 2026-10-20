# AlgebraicGeometry.ProEtale.coefficientBoundedConstructibleProEtale

## Reason

Restore the assigned module at its recorded active path after the cluster-restore
quarantine in coord/rework.tsv (row for this item). The active Lean file is absent;
its archive is preserved at
quarantine/Sheaf/AlgebraicGeometry/CoefficientBoundedConstructibleProEtale.lean.
The delivery restores that file verbatim, including both public imports and the
complete explicit definition. This repairs the missing module; it does not withdraw
or replace its predicate. No source-library file changes.

The affine-local constructibility dependency was repaired separately by G3 and is
already present in the shared sources. Its published object file is still absent,
so a temporary unchanged sandbox copy was compiled alongside this item. Both compiled
cleanly (3.5 and 3.1 seconds). The temporary dependency source is not delivered.

## Old

The active module is absent. The quarantined definition, preserved verbatim, is:

```lean
def coefficientBoundedConstructibleProEtale (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A] :
    ObjectProperty (ConstantCompletion.D (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, v} X) A)) :=
  fun K ↦
    (∀ q : ℤ, Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A
      ((coefficientModelCohomology _ q).obj K)) ∧
    ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((coefficientModelCohomology _ q).obj K)
```

## New

The complete archived module is restored to
lean/Sheaf/AlgebraicGeometry/CoefficientBoundedConstructibleProEtale.lean.
Its definition is identical to the archive:

```lean
def coefficientBoundedConstructibleProEtale (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A] :
    ObjectProperty (ConstantCompletion.D (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, v} X) A)) :=
  fun K ↦
    (∀ q : ℤ, Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A
      ((coefficientModelCohomology _ q).obj K)) ∧
    ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((coefficientModelCohomology _ q).obj K)
```

## Users

The source import/name scan covered both library roots and the quarantine tree.
The active-source downstream query was also run with --allow-missing. The archive
consumers below remain needed; missing active sources do not authorize withdrawal.
All public imports, universes, binders and the definition body are preserved. The
predicate still asks for constructibility in every integer degree and vanishing
outside one ordered finite interval in the standard ordinary derived category.
There is no new completeness, Tor, finite coefficient-set or scheme Noetherianity
condition. The qcqs hypotheses and independent coefficient universe are unchanged.
No target statement or mathematical meaning is altered, so this is restoration,
not a new target-definition interpretation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale | J3 | Restore the complete definition and its public imports. |
| Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison | unclaimed | Quarantined; direct import and predicate applications retain the identical interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Quarantined; direct import retain the identical interface; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian | unclaimed | Quarantined; transitive consumer and predicate applications retain the identical interface; no adaptation. |
| Sheaf.Paper.CondensedOpenExceptionalProjectionFormula | unclaimed | Quarantined; direct import retain the identical interface; no adaptation. |
| Sheaf.Paper.CondensedPointSupertrace | unclaimed | Quarantined; direct import retain the identical interface; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Quarantined; direct import retain the identical interface; no adaptation. |
| Sheaf.Paper.IntegralCohomologicalAdicCriterion | unclaimed | Quarantined; direct import retain the identical interface; no adaptation. |
| Sheaf.Paper.IntegralModelsOperations | unclaimed | Quarantined; direct import retain the identical interface; no adaptation. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | Quarantined; direct import retain the identical interface; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Quarantined; direct import retain the identical interface; no adaptation. |
| Sheaf.SixFunctors.IntegralModelsGenerators | unclaimed | Quarantined; direct import retain the identical interface; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed | Quarantined; direct import retain the identical interface; no adaptation. |

A temporary importer compiled cleanly (3.0 seconds). It checked the full-subcategory
inclusion with the exact ambient constant-ring derived category used by the comparison
consumers, and checked that boundedConstructible, BoundedConstructible,
mem_boundedConstructible_iff and isTriangulated_boundedConstructible_of_weakSerre
are still publicly available. #print axioms for the coefficient predicate reported
exactly propext, Classical.choice and Quot.sound. The temporary importer is not delivered.
No archived consumer is rewritten or restored in this delivery.

The node sk-def-sfb-bounded-constructible retains its Lean attachment, mathematical
statement, proof plan, proof dependencies and tool uses unchanged. No node is deleted,
no unit route is bypassed, and the generic weak-Serre triangulatedness theorem remains
an existing imported declaration with its existing proof obligation.

## Status

landed 20261020T230753-L-610865 2026-10-20 (merge of deliver/J3/Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale)
