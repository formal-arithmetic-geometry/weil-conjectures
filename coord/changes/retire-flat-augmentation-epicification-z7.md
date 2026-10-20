# CochainComplex.exists_boundedAbove_flat_epicification

## Reason

Retire the Sheaf duplicate as assigned in coord/retire-items.tsv and authorized by
coord/changes/retire-sheaf-twins-20261020.md. The upstream theorem has the same output,
for the same universes and sheaf category, with the redundant cover hypothesis removed.
Its proved functorial-flat-cover construction supplies that hypothesis internally.
No upstream file or target statement changes.

## Old

From Sheaf.Algebra.Homology.FlatAugmentationEpicification:

```lean
theorem exists_boundedAbove_flat_epicification
    (hcover : ∀ M : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      ∃ (P : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (p : P ⟶ M),
        SheafOfModules.IsFlat P ∧ Epi p)
    (E H : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) (f : E ⟶ H)
    (hE : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (E.X i))
    (hH : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (H.X i))
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlat (E.X i)) :
    ∃ (F : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) (s : E ⟶ F) (g : F ⟶ H),
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (F.X i)) ∧
      (∀ i : ℤ, SheafOfModules.IsFlat (F.X i)) ∧ QuasiIso s ∧
      (∀ i : ℤ, Epi (g.f i)) ∧ s ≫ g = f
```

## New

Withdraw lean/Sheaf/Algebra/Homology/FlatAugmentationEpicification.lean.
Its sole consumer imports the existing upstream theorem:

```lean
theorem exists_boundedAbove_flat_epicification
    (E H : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) (f : E ⟶ H)
    (hE : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (E.X i))
    (hH : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (H.X i))
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlat (E.X i)) :
    ∃ (F : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) (s : E ⟶ F) (g : F ⟶ H),
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (F.X i)) ∧
      (∀ i : ℤ, SheafOfModules.IsFlat (F.X i)) ∧ QuasiIso s ∧
      (∀ i : ℤ, Epi (g.f i)) ∧ s ≫ g = f
```

The existing upstream declaration is unchanged. The original conditional node statement
is an immediate specialization of this stronger theorem; its Lean attachment now records
the upstream signature verbatim and explains the redundant hypothesis.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.FlatAugmentationEpicification | Z7 | Withdraw duplicate module. |
| Sheaf.Algebra.Homology.FlatTruncationSuccessor | unclaimed | Replace proof import with upstream twin; remove hcover argument at the single call; preserve its entire signature. |

Source search finds exactly this one consumer and one use of the declaration outside the
retired module in its downstream import closure. The source twin's own user already imports
the source twin and requires no change. Other downstream modules see the same signature of
exists_flat_truncation_successor, so need no adaptation.

The import-only consumer adaptation fails at line 126: application type mismatch, hcover
has sort Prop but a CochainComplex is expected. Removing that obsolete argument repairs
it. The now-unused hcover parameter is explicitly retained as a local _hc binding, beside
the existing _hq and _he bindings, to preserve the statement without linter warnings.

The source theorem retains the same bounded identity-disk construction, augmentation,
contraction and homotopy equivalence. Its zero-target and negative-bound cases are unchanged.
No definition changes meaning, and no target review is reopened.

## Status

landed 20261020T144312-L-2264541 2026-10-20 (merge of deliver/Z7/Sheaf.Algebra.Homology.FlatAugmentationEpicification)
