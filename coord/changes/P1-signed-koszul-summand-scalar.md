# CategoryTheory.ringedNegativeKoszulSummand_D₂_term

## Reason

The old Lean transport equation and basis-differential equation omit the earlier-index sign and scalar exponent. Over Z on a point, a_0=2 and m=1 give scalar 2 on one side and 4 on the other. The repair restores the signed powers dictated by ringedNegativeKoszulFactor and the ordered tensor. The transport equation is then proved directly; the existing basis-differential hole is retained with its correct statement.

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
        (ringedKoszulScalar O
          ⟨(ρ ((-1 : A) ^ (I.filter (fun j ↦ j < i)).card * a i ^ (m + 1))).val,
            (ρ ((-1 : A) ^ (I.filter (fun j ↦ j < i)).card *
              a i ^ (m + 1))).property⟩ ≫
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
            ⟨(ρ ((-1 : A) ^ (I.filter (fun j ↦ j < i)).card * a i ^ (m + 1))).val,
              (ρ ((-1 : A) ^ (I.filter (fun j ↦ j < i)).card *
                a i ^ (m + 1))).property⟩ ≫
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
| Sheaf.CategoryTheory.SignedKoszulSummandTermTransport | P1 | Its incorrect unsigned first-power input is repaired to the signed power; the corrected theorem is proved. |
| Sheaf.CategoryTheory.SignedKoszulSummandDifferential | M1 (claim since 2026-10-26T18:13Z) | Forced adaptation. The basis statement `ringedNegativeKoszulBasis_d_succ` (still `sorry`) receives the signed power; its old statement was false (a_0=2, m=1 gives 2 versus 4). The original module does not compile against the repaired item: `exact ringedNegativeKoszulSummand_D₂_term …` at line 180 of `ringedNegativeKoszulSummand_D₂_succ` fails (whnf timeout trying to unify ρ (a i) with ρ ((-1)^k * a i^(m+1))). Its proved full differential theorem keeps its signature and assembly proof. M1 must now prove the corrected statement. |
| Sheaf.CategoryTheory.SignedKoszulTensorCoordinates | unclaimed in the shared claim snapshot | Direct importer of the basis module. Uses only the unchanged full differential theorem; checked against the repair. |

No target statement or definition is changed. Searches in lean/ and quarantine/ find no other uses of either changed declaration. The only DAG citer of either node is lem-cbc-signed-koszul-summand-differential, whose full signed differential is preserved. Its unfinished descendants still use the same unit route. The direct importer SignedKoszulTensorCoordinates is checked but its unchanged copy will not be delivered.

## Status

landed 20261027T012912-L-2345305 2026-10-27 (merge of deliver/P1/Sheaf.CategoryTheory.SignedKoszulSummandTermTransport)
