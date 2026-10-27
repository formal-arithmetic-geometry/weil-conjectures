# spKoszulRightTensor, spKoszulRearrange, spKoszulRightTower, spKoszulRightCoordinatesInv, spKoszulScalar

## Reason

Move the five existing concrete definitions into the coordinate lemma module, which the original module publicly imports. This permits the algebraic half of the proof to be stated without an import cycle. Names, signatures, visibility, and bodies are unchanged; no object is selected from an unproved existence theorem. The existing target theorem signature and its meaning are unchanged.

## Old

In `lean/Sheaf/Algebra/Homology/NilpotentActionKoszulUnit.lean`:

```lean
/-- The existing total tensor bifunctor with its canonical sheaf tensor structure.
Source: Stacks Tag 012Z (blueprint: lem-sp-nilpotent-action-koszul-unit).
This only installs the recorded tensor instances inside a real construction. -/
noncomputable def spKoszulRightTensor :
    CochainComplex (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ ⥤ CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ ⥤ CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ := by
  letI := SheafOfModules.isMonoidal_W_independentCoefficients R
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  exact (MonoidalCategory.curriedTensor (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R))).map₂CochainComplex

/-- Rearrangement of the recorded tower-complex construction, functorially.
Source: Stacks Tag 0941 (blueprint: lem-sp-nilpotent-action-koszul-unit). -/
def spKoszulRearrange :
    (ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) ⥤ CochainComplex (ℕᵒᵖ ⥤
      (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) ℤ where
  obj := koszulTowerComplex R
  map := koszulTowerComplexMap R
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The actual right total tensor tower `Q ⊗ L_(m+1)`, functorial in every complex Q.
Source: Bhatt--Scholze Lemma 3.4.12 and Stacks 012Z
(blueprint: lem-sp-nilpotent-action-koszul-unit). -/
noncomputable def spKoszulRightTower
    (t : (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj
      R)).sections) :
    CochainComplex (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ ⥤ CochainComplex (ℕᵒᵖ ⥤
      (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) ℤ :=
  spKoszulRightTensor R ⋙
    (Functor.whiskeringLeft ℕᵒᵖ (CochainComplex (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
      (CochainComplex (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)).obj (principalKoszulTower R t) ⋙
      spKoszulRearrange R

/-- The two canonical tensor summands, ordered as `(Q^k,Q^(k+1))`.
Source: Stacks 012Z (blueprint: lem-sp-nilpotent-action-koszul-unit).
The first factor uses the degree-zero target of the cone; the second its shifted source. -/
noncomputable def spKoszulRightCoordinatesInv
    (t : (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj
      R)).sections)
    (Q : CochainComplex (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (m : ℕ) (k : ℤ) :
    Q.X k ⊞ Q.X (k + 1) ⟶
      (((spKoszulRightTensor R).obj Q).obj (principalKoszul R t m)).X k := by
  letI := SheafOfModules.isMonoidal_W_independentCoefficients R
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  exact biprod.desc
    ((MonoidalCategory.rightUnitor (Q.X k)).inv ≫
      MonoidalCategory.whiskerLeft (Q.X k)
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj
      R))).inv ≫
          (CochainComplex.mappingCone.inr
            ((CochainComplex.singleFunctor (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) 0).map
              (endoPow (globalSectionMultiplication R t) (m + 1)))).f 0) ≫
      CochainComplex.ιMapBifunctor Q (principalKoszul R t m)
        (MonoidalCategory.curriedTensor (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) k 0 k (add_zero k))
    ((MonoidalCategory.rightUnitor (Q.X (k + 1))).inv ≫
      MonoidalCategory.whiskerLeft (Q.X (k + 1))
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj
      R))).inv ≫
          (CochainComplex.mappingCone.inl
            ((CochainComplex.singleFunctor (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) 0).map
              (endoPow (globalSectionMultiplication R t) (m + 1)))).v 0 (-1) rfl) ≫
      CochainComplex.ιMapBifunctor Q (principalKoszul R t m)
        (MonoidalCategory.curriedTensor (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) (k + 1) (-1) k (add_neg_cancel_right k 1))

/-- Multiplication by the specified global section, using the existing presheaf action.
Source: Bhatt--Scholze Lemma 3.4.12
(blueprint: lem-sp-nilpotent-action-koszul-unit). -/
noncomputable def spKoszulScalar
    (t : (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj
      R)).sections) (M : (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) : M ⟶ M :=
  ⟨PresheafOfModules.sectionsSMul (S := R.obj) M.val ⟨t.val, t.property⟩⟩
```

## New

The following identical declarations are in `lean/Sheaf/Algebra/Homology/NilpotentKoszulCoordinates.lean`; the original module adds `public import Sheaf.Algebra.Homology.NilpotentKoszulCoordinates` and hence reexports them.

```lean
/-- The existing total tensor bifunctor with its canonical sheaf tensor structure.
Source: Stacks Tag 012Z (blueprint: lem-sp-nilpotent-action-koszul-unit).
This only installs the recorded tensor instances inside a real construction. -/
noncomputable def spKoszulRightTensor :
    CochainComplex (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ ⥤ CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ ⥤ CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ := by
  letI := SheafOfModules.isMonoidal_W_independentCoefficients R
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  exact (MonoidalCategory.curriedTensor (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R))).map₂CochainComplex

/-- Rearrangement of the recorded tower-complex construction, functorially.
Source: Stacks Tag 0941 (blueprint: lem-sp-nilpotent-action-koszul-unit). -/
def spKoszulRearrange :
    (ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) ⥤ CochainComplex (ℕᵒᵖ ⥤
      (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) ℤ where
  obj := koszulTowerComplex R
  map := koszulTowerComplexMap R
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The actual right total tensor tower `Q ⊗ L_(m+1)`, functorial in every complex Q.
Source: Bhatt--Scholze Lemma 3.4.12 and Stacks 012Z
(blueprint: lem-sp-nilpotent-action-koszul-unit). -/
noncomputable def spKoszulRightTower
    (t : (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj
      R)).sections) :
    CochainComplex (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ ⥤ CochainComplex (ℕᵒᵖ ⥤
      (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) ℤ :=
  spKoszulRightTensor R ⋙
    (Functor.whiskeringLeft ℕᵒᵖ (CochainComplex (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
      (CochainComplex (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)).obj (principalKoszulTower R t) ⋙
      spKoszulRearrange R

/-- The two canonical tensor summands, ordered as `(Q^k,Q^(k+1))`.
Source: Stacks 012Z (blueprint: lem-sp-nilpotent-action-koszul-unit).
The first factor uses the degree-zero target of the cone; the second its shifted source. -/
noncomputable def spKoszulRightCoordinatesInv
    (t : (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj
      R)).sections)
    (Q : CochainComplex (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (m : ℕ) (k : ℤ) :
    Q.X k ⊞ Q.X (k + 1) ⟶
      (((spKoszulRightTensor R).obj Q).obj (principalKoszul R t m)).X k := by
  letI := SheafOfModules.isMonoidal_W_independentCoefficients R
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  exact biprod.desc
    ((MonoidalCategory.rightUnitor (Q.X k)).inv ≫
      MonoidalCategory.whiskerLeft (Q.X k)
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj
      R))).inv ≫
          (CochainComplex.mappingCone.inr
            ((CochainComplex.singleFunctor (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) 0).map
              (endoPow (globalSectionMultiplication R t) (m + 1)))).f 0) ≫
      CochainComplex.ιMapBifunctor Q (principalKoszul R t m)
        (MonoidalCategory.curriedTensor (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) k 0 k (add_zero k))
    ((MonoidalCategory.rightUnitor (Q.X (k + 1))).inv ≫
      MonoidalCategory.whiskerLeft (Q.X (k + 1))
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj
      R))).inv ≫
          (CochainComplex.mappingCone.inl
            ((CochainComplex.singleFunctor (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) 0).map
              (endoPow (globalSectionMultiplication R t) (m + 1)))).v 0 (-1) rfl) ≫
      CochainComplex.ιMapBifunctor Q (principalKoszul R t m)
        (MonoidalCategory.curriedTensor (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) (k + 1) (-1) k (add_neg_cancel_right k 1))

/-- Multiplication by the specified global section, using the existing presheaf action.
Source: Bhatt--Scholze Lemma 3.4.12
(blueprint: lem-sp-nilpotent-action-koszul-unit). -/
noncomputable def spKoszulScalar
    (t : (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj
      R)).sections) (M : (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) : M ⟶ M :=
  ⟨PresheafOfModules.sectionsSMul (S := R.obj) M.val ⟨t.val, t.property⟩⟩
```

## Users

`tools/downstream.py <original module> --uses <name>` was run for each of the five names. Each reported only the defining module, with no external Lean consumer. No other group module is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.NilpotentActionKoszulUnit | D4 | Uses the identical definitions through the new public import; statement unchanged. |
| Sheaf.Algebra.Homology.NilpotentKoszulCoordinates | D4, new | Owns the identical definitions and states the coordinate lemma. |

## Status

landed 20261025T163612-L-717281 2026-10-25 (merge of deliver/D4/Sheaf.Algebra.Homology.NilpotentActionKoszulUnit)
