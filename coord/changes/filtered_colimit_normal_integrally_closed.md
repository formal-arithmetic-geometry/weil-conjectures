# CommRingCat.integrallyClosed_of_localization_cocone

## Reason

Restore the hypotheses of Stacks Tag 037D: a colimit cocone and normal domains.
The old common-stage claim is false: the diagram constant at Z over a one-object
category has a cocone to Z[√5], which is not integrally closed (its integral fraction
(1+√5)/2 is absent). A cocone witness does not imply a colimit witness.
The source explicitly reduces to normal domains; the original localized theorem
stated a stronger integral-closedness-only generalization. This delivery proves the
source's domain case and updates its only caller, without altering the parent theorem.

## Old

```lean
theorem integrallyClosed_of_localization_cocone
    {I : Type u} [SmallCategory I] [IsFiltered I]
    {R : Type u} [CommRing R]
    (D : I ⥤ CommRingCat.{u})
    (c : Cocone D) (hc : c.pt = CommRingCat.of R)
    (hD : ∀ i : I, IsIntegrallyClosed (D.obj i)) :
    IsIntegrallyClosed R
```

```lean
theorem filtered_colimit_localization_isIntegrallyClosed
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F]
    (hF : ∀ i : I, ∀ (p : Ideal (F.obj i)) [p.IsPrime],
      IsIntegrallyClosed (Localization.AtPrime p))
    (p : Ideal ((colimit F : CommRingCat.{u}) : Type u)) [p.IsPrime] :
    IsIntegrallyClosed (Localization.AtPrime p)
```

## New

```lean
theorem integrallyClosed_of_localization_cocone
    {I : Type u} [SmallCategory I] [IsFiltered I]
    {R : Type u} [CommRing R]
    (D : I ⥤ CommRingCat.{u})
    (c : Cocone D) (hc : c.pt = CommRingCat.of R) (hcol : IsColimit c)
    (hD : ∀ i : I, IsDomain (D.obj i) ∧ IsIntegrallyClosed (D.obj i)) :
    IsIntegrallyClosed R
```

```lean
theorem filtered_colimit_localization_isIntegrallyClosed
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F]
    (hF : ∀ i : I, ∀ (p : Ideal (F.obj i)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (p : Ideal ((colimit F : CommRingCat.{u}) : Type u)) [p.IsPrime] :
    IsIntegrallyClosed (Localization.AtPrime p)
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.FilteredColimitNormalRingIntegrallyClosed | S1 | Pass the existing colimit witness and both stage hypotheses to the helper. |
| Sheaf.RingTheory.FilteredColimitNormalRing | none recorded | Pass hF directly; its statement already includes domain hypotheses and is unchanged. |

All 176 transitive importers keep their statements and definitions unchanged:
there are no changed definitions, public imports or target statements.
The only textual caller of either changed theorem is the parent shown above.

## Status

landed 20261012T135314-L-1691353 2026-10-12 (merge of deliver/S1/Sheaf.RingTheory.FilteredColimitNormalRingIntegrallyClosed)
