# AlgebraicGeometry.Etale.SupportProjectionCoherent

## Reason

The unit arrows are now named `supportProjectionUnitA` and `supportProjectionUnitB`,
with exactly their original bodies. The concrete conjunction unfolds the signed derived tensor and nested sheaf
localization instances when packaging an invertible projection map. Kernel checking
that specialization exceeds the per-file limit. Express the identical conjunction
through an abbreviation of a generic bifunctor predicate, so the inverse coherence proof is checked
before specializing to sheaves. A private helper takes the projection map and its
forward equations as arguments, then specializes to the fixed map. This prevents
the kernel from expanding that map while checking the generic theorem application. The map equality, both integer-shift conditions,
and both equations using the specified unit arrows are preserved. The generic
predicate explicitly uses the existing `supportProjectionSourceCommShift` and
`supportProjectionTargetCommShift` families. No target
statement changes. The coefficient object is inferred from the domain types of the
two unit arrows and is the original tensor unit. Targets using this definition
require the normal meaning review.

## Old

```lean
def SupportProjectionCoherent
    (e : supportProjectionSource A c ≅ supportProjectionTarget A c) : Prop :=
  e.hom = supportProjectionMap A c ∧
      (∀ K : DerivedCategory (Sheaf X.smallEtaleTopology A),
        NatTrans.CommShift (e.hom.app K) ℤ ∧
        NatTrans.CommShift (e.inv.app K) ℤ ∧
        ((e.hom.app K).app (𝟙_ _) ≫
          (supportProjectionTargetUnit A c K).hom =
            (derivedTensorLeftUnitor A Y
              ((rightDerivedLowerShriekOfCompactification A c).obj K)).hom) ∧
        ((e.inv.app K).app (𝟙_ _) ≫
          (derivedTensorLeftUnitor A Y
            ((rightDerivedLowerShriekOfCompactification A c).obj K)).hom =
              (supportProjectionTargetUnit A c K).hom))
```

## New

```lean
noncomputable def supportProjectionUnitA
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((supportProjectionTarget A c).obj K).obj
      (𝟙_ (DerivedCategory (Sheaf Y.smallEtaleTopology A))) ⟶
      (rightDerivedLowerShriekOfCompactification A c).obj K :=
  (supportProjectionTargetUnit A c K).hom

/-- The source unit arrow of the support projection.
Source: Zheng Theorem 2.18(2) (blueprint: lem-pur-etale-support-projection-shift-unit). -/
noncomputable def supportProjectionUnitB
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((supportProjectionSource A c).obj K).obj
      (𝟙_ (DerivedCategory (Sheaf Y.smallEtaleTopology A))) ⟶
      (rightDerivedLowerShriekOfCompactification A c).obj K :=
  (derivedTensorLeftUnitor A Y
    ((rightDerivedLowerShriekOfCompactification A c).obj K)).hom

/-- The actual map, its canonical integer-shift square (in both directions), and
its identity component at the coefficient unit, using the explicitly fixed unitors.
Source: Zheng Theorem 2.18(2), Stacks Tags 0B56 and 0GL1
(blueprint: lem-pur-etale-support-projection-shift-unit). -/
abbrev SupportProjectionCoherent
    (e : supportProjectionSource A c ≅ supportProjectionTarget A c) : Prop :=
  BifunctorProjectionCoherent (sT := supportProjectionSourceCommShift A c)
    (sU := supportProjectionTargetCommShift A c)
    e (supportProjectionMap A c) _
    (fun K ↦ (rightDerivedLowerShriekOfCompactification A c).obj K)
    (supportProjectionUnitA A c)
    (supportProjectionUnitB A c)
```

`CategoryTheory.BifunctorProjectionCoherent` is defined in
`Sheaf.CategoryTheory.BifunctorProjectionCoherence` by exactly the original
conjunction. Its theorem constructs `asIso`, applies `NatTrans.CommShift.of_iso_inv`,
and proves the inverse unit equation by cancellation.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleSupportProjectionShiftUnit | P6 | Same conditions, generic specialization. |
| Sheaf.Paper.SystemCompactSupportEvaluation | unclaimed | Imports item; no use of changed definition. |
| Sheaf.Paper.SystemCompactSupportProjection | unclaimed | Imports item; no use of changed definition. |

## Status

landed 20261026T002138-L-60288 2026-10-26 (merge of deliver/P6/Sheaf.AlgebraicGeometry.EtaleSupportProjectionShiftUnit)
