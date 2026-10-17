# Private coefficient-exchange component signatures

## Reason

The delivery tool rejects all compiler warnings, including the baseline long-line
warnings in three private signatures. Wrap only those signatures to at most 100
characters per line. Their Lean tokens, universes, hypotheses, conclusions and
visibility are identical. No mathematical statement, construction or target meaning
changes. This record explicitly declares the whitespace-only signature differences
required by the second-reading brief.

## Old

```lean
private lemma restricted_comp_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {T U : Scheme.{u}} [T.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]
    {V : Scheme.{u}} [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))] (j : U ⟶ V) [j.IsOver (Spec (.of k))]
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ V)) :
    ((boundedConstructibleUpperStarComp Λ ℓ (h.asOver (Spec (.of k))) (j.asOver (Spec (.of k)))).hom.app K).hom =
      (leftDerivedUpperStarComp Λ h j).hom.app K.obj

private lemma unit_step_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ X)) :
    ((boundedConstructibleBaseChangeUnitStep Λ ℓ (f.asOver (Spec (.of k))) (g.asOver (Spec (.of k))) (f'.asOver (Spec (.of k)))).app K).hom =
      (coefficientDerivedAdjunction Λ f').unit.app
        ((coefficientDerivedUpperStar Λ g).obj
          ((coefficientDerivedLowerStar Λ f).obj K.obj))

private lemma counit_step_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ X)) :
    ((boundedConstructibleBaseChangeCounitStep Λ ℓ (f.asOver (Spec (.of k))) (f'.asOver (Spec (.of k))) (g'.asOver (Spec (.of k)))).app K).hom =
      (coefficientDerivedLowerStar Λ f').map
        ((coefficientDerivedUpperStar Λ g').map
          ((coefficientDerivedAdjunction Λ f).counit.app K.obj))
```

## New

```lean
private lemma restricted_comp_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {T U : Scheme.{u}} [T.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]
    {V : Scheme.{u}} [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))] (j : U ⟶ V) [j.IsOver (Spec (.of k))]
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ V)) :
    ((boundedConstructibleUpperStarComp Λ ℓ
      (h.asOver (Spec (.of k))) (j.asOver (Spec (.of k)))).hom.app K).hom =
      (leftDerivedUpperStarComp Λ h j).hom.app K.obj

private lemma unit_step_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ X)) :
    ((boundedConstructibleBaseChangeUnitStep Λ ℓ
      (f.asOver (Spec (.of k))) (g.asOver (Spec (.of k)))
      (f'.asOver (Spec (.of k)))).app K).hom =
      (coefficientDerivedAdjunction Λ f').unit.app
        ((coefficientDerivedUpperStar Λ g).obj
          ((coefficientDerivedLowerStar Λ f).obj K.obj))

private lemma counit_step_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ X)) :
    ((boundedConstructibleBaseChangeCounitStep Λ ℓ
      (f.asOver (Spec (.of k))) (f'.asOver (Spec (.of k)))
      (g'.asOver (Spec (.of k)))).app K).hom =
      (coefficientDerivedLowerStar Λ f').map
        ((coefficientDerivedUpperStar Λ g').map
          ((coefficientDerivedAdjunction Λ f).counit.app K.obj))
```

## Users

These declarations are private, so no other module can use them. Textual searches
of both library roots found no external reference to these names. Their only
consumer is the item module itself. No downstream module needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientExchangeFromComparisons | A4 | Signature whitespace only; identical elaborated types. |

## Status

landed 20261017T031541-L-1622036 2026-10-17 (merge of deliver/A4/Sheaf.Paper.CoefficientExchangeFromComparisons)
