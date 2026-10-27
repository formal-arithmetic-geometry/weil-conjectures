# CategoryTheory.ringedNegativeKoszulBasis_d_succ

## Reason

The Lean summand omitted both the ordered-tensor sign and the exponent m+1. Over the one-point site with O=Z, one factor, a_0=2 and m=1, the old equality says multiplication by 4 equals multiplication by 2. With two factors, m=0, both a_i=1 and I={0,1}, the second erasure must have the opposite sign. The correction follows the already-defined negative factors and ordered total tensor.

## Old

```lean
theorem ringedNegativeKoszulBasis_d_succ
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) {A : Type z} [CommRing A]
    (ρ : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
    (r : ℕ) (a : Fin (r + 1) → A) (m : ℕ) (I : Finset (Fin (r + 1))) :
    letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
      SheafOfModules.isGrothendieckAbelian _
    letI := SheafOfModules.monoidalCategory O
    letI := SheafOfModules.symmetricCategory O
    letI := Classical.choice (SheafOfModules.tensorClosed O).1
    letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
    ringedNegativeKoszulBasis O (r + 1)
        (fun i ↦ ⟨(ρ (a i)).val, (ρ (a i)).property⟩) m I (-(I.card : ℤ)) ≫
      (ringedNegativeKoszul O (r + 1)
        (fun i ↦ ⟨(ρ (a i)).val, (ρ (a i)).property⟩) m).d
        (-(I.card : ℤ)) (-(I.card : ℤ) + 1) =
      ∑ i ∈ I, if h : -(I.card : ℤ) + 1 = -((I.erase i).card : ℤ) then
        ringedKoszulScalar O
            ⟨(ρ (a i)).val, (ρ (a i)).property⟩ ≫
          ringedNegativeKoszulBasis O (r + 1)
            (fun j ↦ ⟨(ρ (a j)).val, (ρ (a j)).property⟩) m
            (I.erase i) (-((I.erase i).card : ℤ)) ≫
          eqToHom (congrArg
            (ringedNegativeKoszul O (r + 1)
              (fun j ↦ ⟨(ρ (a j)).val, (ρ (a j)).property⟩) m).X h.symm)
      else 0
```

## New

```lean
theorem ringedNegativeKoszulBasis_d_succ
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) {A : Type z} [CommRing A]
    (ρ : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
    (r : ℕ) (a : Fin (r + 1) → A) (m : ℕ) (I : Finset (Fin (r + 1))) :
    letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
      SheafOfModules.isGrothendieckAbelian _
    letI := SheafOfModules.monoidalCategory O
    letI := SheafOfModules.symmetricCategory O
    letI := Classical.choice (SheafOfModules.tensorClosed O).1
    letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
    ringedNegativeKoszulBasis O (r + 1)
        (fun i ↦ ⟨(ρ (a i)).val, (ρ (a i)).property⟩) m I (-(I.card : ℤ)) ≫
      (ringedNegativeKoszul O (r + 1)
        (fun i ↦ ⟨(ρ (a i)).val, (ρ (a i)).property⟩) m).d
        (-(I.card : ℤ)) (-(I.card : ℤ) + 1) =
      ∑ i ∈ I, if h : -(I.card : ℤ) + 1 = -((I.erase i).card : ℤ) then
        ((-1 : ℤ) ^ (I.filter (fun j ↦ j < i)).card •
            (ringedKoszulScalar O ⟨(ρ (a i)).val, (ρ (a i)).property⟩) ^ (m + 1)) ≫
          ringedNegativeKoszulBasis O (r + 1)
            (fun j ↦ ⟨(ρ (a j)).val, (ρ (a j)).property⟩) m
            (I.erase i) (-((I.erase i).card : ℤ)) ≫
          eqToHom (congrArg
            (ringedNegativeKoszul O (r + 1)
              (fun j ↦ ⟨(ρ (a j)).val, (ρ (a j)).property⟩) m).X h.symm)
      else 0
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.SignedKoszulSummandDifferential | M1 | The summand proof still uses the basis differential, now with the correct signed power. Its conclusion and hypotheses are unchanged; the matching term-transport statement is repaired in the same delivery. |
| Sheaf.CategoryTheory.SignedKoszulTensorCoordinates | unclaimed | Direct importer; the exported summand theorem is unchanged. Recompile against the repair. |

No definition or target statement changes. The unit route is unchanged.

## Status

landed 20261026T222733-L-687964 2026-10-26 (merge of deliver/M1/Sheaf.CategoryTheory.SignedKoszulSummandDifferential)
