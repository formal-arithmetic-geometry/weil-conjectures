# WeilConjectures.realizationScalarTargetTriangulated

## Reason

Restore the quarantined RealizationScalarFunctor interface after upstream sync ee65497e6.
The source's isTriangulated_boundedConstructible now requires IsFinitenessCoefficient.
Its continuous constructor uses E : Type, while this interface has E : Type u.
Consequently the target HasShift required by the shift field could not be synthesized.
The initial published-build compile exposed the previous unrestricted instance. Later
inspection of the refreshed build confirmed the restricted source signature. The repair
is checked independently with that upstream instance disabled in a scratch copy.

## Old

No realizationScalarTargetTriangulated declaration. The unchanged record contains:

```lean
  [shift : J.CommShift ℤ]
  exact : J.IsTriangulated
```

These fields previously relied on the upstream unrestricted triangulation instance.

## New

```lean
set_option synthInstance.checkSynthOrder false in
/-- Continuous field coefficients in the scheme universe have the inherited bounded
constructible triangulation. Source: Bhatt--Scholze, Proposition 6.8.11(1),(3).
(blueprint: lem-weil-pbc-realization-scalar-functor)

Proof. Local finite presentations over these coefficients are pro-etale locally finite
free. The constructible Serre argument therefore supplies kernel, cokernel and extension
closure on the noetherian strata. The bounded homology Serre criterion gives triangulated
closure, including zero ranks and the empty scheme. -/
instance realizationScalarTargetTriangulated :
    (boundedConstructible
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) T)).IsTriangulated := by
  obtain ⟨hk, he⟩ := condensed_constructible_serre_of_locally_free freeEpiLocalSplitting
    (Profinite.continuousCoefficientRingObj E)
    (exists_finiteFree_cover_of_condensedField_lfp l E) T
  let R := condensedRingObj (Profinite.continuousCoefficientRingObj E) T
  let : ObjectProperty.IsClosedUnderKernels (IsConstructibleModuleObject R) :=
    ⟨by
      rintro _ ⟨f, s, hs, hf⟩
      exact IsConstructibleModuleObject.of_iso (R := R) (limit.isoLimitCone ⟨s, hs⟩)
        (hk _ _ f hf.1 hf.2).1⟩
  let : ObjectProperty.IsClosedUnderCokernels (IsConstructibleModuleObject R) :=
    ⟨by
      rintro _ ⟨f, s, hs, hf⟩
      exact IsConstructibleModuleObject.of_iso (R := R) (colimit.isoColimitCocone ⟨s, hs⟩)
        (hk _ _ f hf.1 hf.2).2⟩
  let : ObjectProperty.IsClosedUnderExtensions (IsConstructibleModuleObject R) := ⟨he _⟩
  exact isTriangulated_boundedConstructible_of_serre R
```

The instance proves closure for exactly the same boundedConstructible predicate and
continuousCoefficientRingObj E, with E in the scheme universe. It uses the existing
local finite freeness theorem and the private generic Serre argument, followed by
isTriangulated_boundedConstructible_of_serre. The all import is private and used only
in this proof. The existing record, its fields, and realization_scalar_functor have
unchanged source signatures and bodies. No coefficient, category, morphism, shift or
triangle is redefined. The target statement and its meaning are unchanged; the new
proof supplies the intended inherited triangulation and adds no hypothesis.

## Users

The live downstream.py --allow-missing inventory has no users because the item and
all ten descendants are quarantined. The following inventory also reads quarantine
sources; every direct and transitive consumer is listed. No consumer constructs the
record or requires a changed signature. No adaptation is needed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.RealizationAdjointComparisons | unclaimed | Direct importer; existing projections and theorem unchanged. |
| Sheaf.Paper.RealizationCoefficientSquare | unclaimed | Direct importer; existing projections and theorem unchanged. |
| Sheaf.Paper.RealizationCompletedImage | unclaimed | Direct importer; existing projections and theorem unchanged. |
| Sheaf.Paper.RealizationCompletedPull | unclaimed | Transitive importer; no interface adaptation. |
| Sheaf.Paper.RealizationCompletedPullData | unclaimed | Direct importer; existing projections and theorem unchanged. |
| Sheaf.Paper.RealizationContinuousDirectImage | unclaimed | Direct importer; existing projections and theorem unchanged. |
| Sheaf.Paper.RealizationLocalizedPush | unclaimed | Direct importer; existing projections and theorem unchanged. |
| Sheaf.Paper.RealizationPullOrdinarySystem | unclaimed | Transitive importer; no interface adaptation. |
| Sheaf.Paper.RealizationPullRationalDescent | unclaimed | Transitive importer; no interface adaptation. |
| Sheaf.Paper.RealizationScalarPushMate | unclaimed | Direct importer; existing projections and theorem unchanged. |

All eleven files (the repaired item and these ten unchanged consumer copies) passed
lcompile in import order. A separate scratch copy of the item also compiled with the
upstream isTriangulated_boundedConstructible instance disabled. No consumer source is
changed or restored by this delivery; their quarantines remain available to their owners.

## Status

landed 20261022T113910-L-382550 2026-10-22 (merge of deliver/D3/Sheaf.Paper.RealizationScalarFunctor)
