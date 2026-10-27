# CategoryTheory.ringedNegativeKoszulSummand_D₂_term

## Reason

The left side used the unsigned first power of a_i although the right side used its signed (m+1)-st power. For one factor, m=1, a_0=2, K=O[0], q=-1 and I={0}, the old statement equates multiplication by 2 and 4. Insert the signed power on the left; the right side and all hypotheses stay unchanged.

## Old

```lean
theorem ringedNegativeKoszulSummand_D₂_term
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) {A : Type z} [CommRing A]
    (ρ : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
    (r : ℕ) (a : Fin (r + 1) → A) (m : ℕ) (K : ringedSiteComplex O) (q : ℤ)
    (I : Finset (Fin (r + 1))) (i : Fin (r + 1)) (hi : i ∈ I)
    (hdeg : q + (I.card : ℤ) = (q + 1) + ((I.erase i).card : ℤ))
    (hsrc : -(I.card : ℤ) + 1 = -((I.erase i).card : ℤ)) :
    letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
      SheafOfModules.isGrothendieckAbelian _
    letI := SheafOfModules.monoidalCategory O
    letI := SheafOfModules.symmetricCategory O
    letI := Classical.choice (SheafOfModules.tensorClosed O).1
    letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
    let Q := ringedNegativeKoszul O (r + 1)
      (fun j ↦ ⟨(ρ (a j)).val, (ρ (a j)).property⟩) m
    ((-1 : ℤˣ) ^ (q + (I.card : ℤ))) •
        (MonoidalCategory.rightUnitor (K.X (q + I.card))).inv ≫
      (MonoidalCategory.tensorLeft (K.X (q + I.card))).map
        (ringedKoszulScalar O ⟨(ρ (a i)).val, (ρ (a i)).property⟩ ≫
          ringedNegativeKoszulBasis O
            (r + 1) (fun j ↦ ⟨(ρ (a j)).val, (ρ (a j)).property⟩) m
            (I.erase i) (-((I.erase i).card : ℤ)) ≫
          eqToHom (congrArg Q.X hsrc.symm)) ≫
      CochainComplex.ιMapBifunctor K Q (MonoidalCategory.curriedTensor _)
        (q + I.card) (-(I.card : ℤ) + 1) (q + 1) (by omega) =
      ringedKoszulCoefficientSMul O ρ
          ((if Even (q + (I.card : ℤ)) then (1 : A) else -1) *
            (-1 : A) ^ (I.filter (fun j ↦ j < i)).card * a i ^ (m + 1))
        (K.XIsoOfEq hdeg).hom ≫
        (MonoidalCategory.rightUnitor (K.X (q + 1 + (I.erase i).card))).inv ≫
        (MonoidalCategory.tensorHom (𝟙 _) 
          (ringedNegativeKoszulBasis O
            (r + 1) (fun j ↦ ⟨(ρ (a j)).val, (ρ (a j)).property⟩) m
            (I.erase i) (-((I.erase i).card : ℤ)))) ≫
        CochainComplex.ιMapBifunctor K Q (MonoidalCategory.curriedTensor _)
          (q + 1 + (I.erase i).card) (-((I.erase i).card : ℤ)) (q + 1) (by omega)
```

## New

```lean
theorem ringedNegativeKoszulSummand_D₂_term
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) {A : Type z} [CommRing A]
    (ρ : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
    (r : ℕ) (a : Fin (r + 1) → A) (m : ℕ) (K : ringedSiteComplex O) (q : ℤ)
    (I : Finset (Fin (r + 1))) (i : Fin (r + 1)) (hi : i ∈ I)
    (hdeg : q + (I.card : ℤ) = (q + 1) + ((I.erase i).card : ℤ))
    (hsrc : -(I.card : ℤ) + 1 = -((I.erase i).card : ℤ)) :
    letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
      SheafOfModules.isGrothendieckAbelian _
    letI := SheafOfModules.monoidalCategory O
    letI := SheafOfModules.symmetricCategory O
    letI := Classical.choice (SheafOfModules.tensorClosed O).1
    letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
    let Q := ringedNegativeKoszul O (r + 1)
      (fun j ↦ ⟨(ρ (a j)).val, (ρ (a j)).property⟩) m
    ((-1 : ℤˣ) ^ (q + (I.card : ℤ))) •
        (MonoidalCategory.rightUnitor (K.X (q + I.card))).inv ≫
      (MonoidalCategory.tensorLeft (K.X (q + I.card))).map
        (((-1 : ℤ) ^ (I.filter (fun j ↦ j < i)).card •
            (ringedKoszulScalar O ⟨(ρ (a i)).val, (ρ (a i)).property⟩) ^ (m + 1)) ≫
          ringedNegativeKoszulBasis O
            (r + 1) (fun j ↦ ⟨(ρ (a j)).val, (ρ (a j)).property⟩) m
            (I.erase i) (-((I.erase i).card : ℤ)) ≫
          eqToHom (congrArg Q.X hsrc.symm)) ≫
      CochainComplex.ιMapBifunctor K Q (MonoidalCategory.curriedTensor _)
        (q + I.card) (-(I.card : ℤ) + 1) (q + 1) (by omega) =
      ringedKoszulCoefficientSMul O ρ
          ((if Even (q + (I.card : ℤ)) then (1 : A) else -1) *
            (-1 : A) ^ (I.filter (fun j ↦ j < i)).card * a i ^ (m + 1))
        (K.XIsoOfEq hdeg).hom ≫
        (MonoidalCategory.rightUnitor (K.X (q + 1 + (I.erase i).card))).inv ≫
        (MonoidalCategory.tensorHom (𝟙 _) 
          (ringedNegativeKoszulBasis O
            (r + 1) (fun j ↦ ⟨(ρ (a j)).val, (ρ (a j)).property⟩) m
            (I.erase i) (-((I.erase i).card : ℤ)))) ≫
        CochainComplex.ιMapBifunctor K Q (MonoidalCategory.curriedTensor _)
          (q + 1 + (I.erase i).card) (-((I.erase i).card : ℤ)) (q + 1) (by omega)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.SignedKoszulSummandDifferential | M1 | The sole consumer applies this term equality to each summand of the basis differential. The repaired left side is exactly the term of the repaired basis theorem; the consumer conclusion is unchanged. |
| Sheaf.CategoryTheory.SignedKoszulSummandTermTransport | P1 (claim since 2026-10-26T18:15Z) | Its own false statement is corrected; its existing proof hole remains. Forced: the item's proved `ringedNegativeKoszulSummand_D₂_succ` applies this theorem to each summand of the corrected basis differential, and the old left side (unsigned first power) neither matches that summand nor is true. P1 must prove the corrected statement. |

No definition or target statement changes. The unit route is unchanged.

## Status

landed 20261026T222733-L-687964 2026-10-26 (merge of deliver/M1/Sheaf.CategoryTheory.SignedKoszulSummandDifferential)
