# AlgebraicGeometry.Etale.rawTriangleMap

## Reason

Landing-conflict repair: use the current coefficient-square source, preserve its newly landed shift-transport proof and structural-exact import, and reapply only the factor relocation and public canonical re-export. No proof hole from the old delivery is restored.

The raw Over pullback and its displayed factors reconstructed equal single-complex and inverse-image data independently. Expanding those large category instances made the concrete associativity proof exceed the file limit. Share the first two factors as `rawTriangleSource` and reuse the existing named raw coefficient and complex. This is a refactoring of the same maps: `Category.assoc` identifies the old and new generic raw triangle composites, and the module coefficient body expands to its old expression. No target statement or public signature changes.

The two existing module and abelian coefficient definitions move together to `RawModuleScalarCoefficientFactors`; `RawModuleScalarCoefficientSquare` publicly re-exports the canonical module. This lets the module formula use only definitions, with no dependency on the coefficient-square theorem. The scalar factor remains byte-for-byte unchanged in RawModuleScalarCoefficientSquare; no new copy of it is defined. RawModuleScalarMapFormula is not changed or imported by the new factors module. RawModuleScalarSourceFactors now directly publicly imports HigherDirectImageRawTrianglePullback, the prerequisite used by its changed definition body; the existing transitive re-export is retained. The new factor module imports HigherDirectImageRawOverCoefficient and CohomologyPresheaf; it needs neither the scalar comparison construction nor the unshifted coefficient theorem.

## Old

In `HigherDirectImageRawTrianglePullback`:

```lean
def rawTriangleMap
    {C D E D' E' : Type*}
    [Category C] [Category D] [Category E] [Category D'] [Category E']
    [Preadditive D'] [Preadditive E']
    (H : C ⥤ D) (H' : C ⥤ E) (P : D ⥤ E)
    (A : D ⥤ D') (B : E ⥤ E') (F : D' ⥤ E')
    (c : H' ⟶ H ⋙ P) (e : P ⋙ B ⟶ A ⋙ F)
    (U : C) {K : D'} {K' : E'}
    (z : ((H ⋙ A).op ⋙ preadditiveYoneda.obj K).obj (op U))
    (s : F.obj K ⟶ K') :
    ((H' ⋙ B).op ⋙ preadditiveYoneda.obj K').obj (op U) :=
  B.map (c.app U) ≫ e.app (H.obj U) ≫ F.map z ≫ s
```

In `RawModuleScalarSourceFactors`:

```lean
noncomputable def moduleSourceFactor
    (Λ : Type (u + 1)) [CommRing Λ] {S Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar (ModuleCat.{u + 1} Λ) h').obj L) ⟶
      (upperStar (ModuleCat.{u + 1} Λ) a).mapDerivedCategoryPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar (ModuleCat.{u + 1} Λ) h).obj L)) :=
  (DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStarComp (ModuleCat.{u + 1} Λ) a h h' w.symm).hom.app L) ≫
    ((upperStar (ModuleCat.{u + 1} Λ) a).mapDerivedCategoryPlusSingleFunctor 0).inv.app
      ((upperStar (ModuleCat.{u + 1} Λ) h).obj L)
```

In `RawModuleScalarCoefficientSquare`:

```lean
noncomputable def moduleCoefficientFactor
    (Λ : Type (u + 1)) [CommRing Λ] {W : Scheme.{u}}
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (A B : Over W) (f : A ⟶ B) :
    (upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus.obj
        (((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar (ModuleCat.{u + 1} Λ) B.hom).obj G))⟦q⟧) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar (ModuleCat.{u + 1} Λ) A.hom).obj G))⟦q⟧ :=
  ((upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus.commShiftIso q).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar (ModuleCat.{u + 1} Λ) B.hom).obj G)) ≫
    (shiftFunctor _ q).map
      (((upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlusSingleFunctor 0).hom.app
          ((upperStar (ModuleCat.{u + 1} Λ) B.hom).obj G) ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map
          ((upperStarComp (ModuleCat.{u + 1} Λ) f.left B.hom A.hom
            (Over.w f).symm).inv.app G))
```

In `RawModuleScalarCoefficientSquare`:

```lean
noncomputable def abelianCoefficientFactor
    {W : Scheme.{u}} (G : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)
    (A B : Over W) (f : A ⟶ B) :
    (upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.obj
        (((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar AddCommGrpCat.{u + 1} B.hom).obj G))⟦q⟧) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar AddCommGrpCat.{u + 1} A.hom).obj G))⟦q⟧ :=
  ((upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.commShiftIso q).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar AddCommGrpCat.{u + 1} B.hom).obj G)) ≫
    (shiftFunctor _ q).map
      (((upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map
          ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
            (Over.w f).symm).inv.app G))
```

In `HigherDirectImageRawDiagram`, the two private generic helper signatures (only regrouped by associativity):

```lean
private theorem five_factor_add
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] {X Y : C} {P Q R T : D}
    (a : P ⟶ Q) (b : Q ⟶ F.obj X) (c : F.obj Y ⟶ R) (d : R ⟶ T)
    (x y : X ⟶ Y) :
    a ≫ b ≫ F.map (x + y) ≫ c ≫ d =
      (a ≫ b ≫ F.map x ≫ c ≫ d) + (a ≫ b ≫ F.map y ≫ c ≫ d) := by
  simp only [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]

private theorem five_factor_zero
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] {X Y : C} {P Q R T : D}
    (a : P ⟶ Q) (b : Q ⟶ F.obj X) (c : F.obj Y ⟶ R) (d : R ⟶ T) :
    a ≫ b ≫ F.map (0 : X ⟶ Y) ≫ c ≫ d = 0 := by
  simp only [Functor.map_zero, Limits.comp_zero, Limits.zero_comp]
```

## New

In `HigherDirectImageRawTrianglePullback`:

```lean
def rawTriangleSource
    {C D E D' E' : Type*}
    [Category C] [Category D] [Category E] [Category D'] [Category E']
    (H : C ⥤ D) (H' : C ⥤ E) (P : D ⥤ E)
    (A : D ⥤ D') (B : E ⥤ E') (F : D' ⥤ E')
    (c : H' ⟶ H ⋙ P) (e : P ⋙ B ⟶ A ⋙ F) (U : C) :
    B.obj (H'.obj U) ⟶ F.obj (A.obj (H.obj U)) :=
  B.map (c.app U) ≫ e.app (H.obj U)
```

In `HigherDirectImageRawTrianglePullback`:

```lean
def rawTriangleMap
    {C D E D' E' : Type*}
    [Category C] [Category D] [Category E] [Category D'] [Category E']
    [Preadditive D'] [Preadditive E']
    (H : C ⥤ D) (H' : C ⥤ E) (P : D ⥤ E)
    (A : D ⥤ D') (B : E ⥤ E') (F : D' ⥤ E')
    (c : H' ⟶ H ⋙ P) (e : P ⋙ B ⟶ A ⋙ F)
    (U : C) {K : D'} {K' : E'}
    (z : ((H ⋙ A).op ⋙ preadditiveYoneda.obj K).obj (op U))
    (s : F.obj K ⟶ K') :
    ((H' ⋙ B).op ⋙ preadditiveYoneda.obj K').obj (op U) :=
  rawTriangleSource H H' P A B F c e U ≫ F.map z ≫ s
```

In `RawModuleScalarSourceFactors`:

```lean
noncomputable def moduleSourceFactor
    (Λ : Type (u + 1)) [CommRing Λ] {S Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar (ModuleCat.{u + 1} Λ) h').obj L) ⟶
      (upperStar (ModuleCat.{u + 1} Λ) a).mapDerivedCategoryPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar (ModuleCat.{u + 1} Λ) h).obj L)) :=
  rawTriangleSource (upperStar (ModuleCat.{u + 1} Λ) h) (upperStar (ModuleCat.{u + 1} Λ) h')
    (upperStar (ModuleCat.{u + 1} Λ) a)
    (DerivedCategory.Plus.singleFunctor _ 0) (DerivedCategory.Plus.singleFunctor _ 0)
    (upperStar (ModuleCat.{u + 1} Λ) a).mapDerivedCategoryPlus
    (upperStarComp (ModuleCat.{u + 1} Λ) a h h' w.symm).hom
    ((upperStar (ModuleCat.{u + 1} Λ) a).mapDerivedCategoryPlusSingleFunctor 0).inv L
```

In `RawModuleScalarCoefficientFactors`:

```lean
noncomputable def moduleCoefficientFactor
    (Λ : Type (u + 1)) [CommRing Λ] {W : Scheme.{u}}
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (A B : Over W) (f : A ⟶ B) :
    (upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus.obj
        (((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar (ModuleCat.{u + 1} Λ) B.hom).obj G))⟦q⟧) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar (ModuleCat.{u + 1} Λ) A.hom).obj G))⟦q⟧ :=
  ((moduleUpperStar Λ f.left).mapDerivedCategoryPlus.commShiftIso q).hom.app
    (higherDirectImageRawOverComplex Λ G B) ≫
    (shiftFunctor _ q).map (higherDirectImageRawOverCoefficient Λ G f)
```

In `RawModuleScalarCoefficientFactors`:

```lean
noncomputable def abelianCoefficientFactor
    {W : Scheme.{u}} (G : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)
    (A B : Over W) (f : A ⟶ B) :
    (upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.obj
        (((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar AddCommGrpCat.{u + 1} B.hom).obj G))⟦q⟧) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar AddCommGrpCat.{u + 1} A.hom).obj G))⟦q⟧ :=
  ((upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.commShiftIso q).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar AddCommGrpCat.{u + 1} B.hom).obj G)) ≫
    (shiftFunctor _ q).map
      (((upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map
          ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
            (Over.w f).symm).inv.app G))
```

In `HigherDirectImageRawDiagram`, the two private generic helper signatures (only regrouped by associativity):

```lean
private theorem five_factor_add
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] {X Y : C} {P Q R T : D}
    (a : P ⟶ Q) (b : Q ⟶ F.obj X) (c : F.obj Y ⟶ R) (d : R ⟶ T)
    (x y : X ⟶ Y) :
    (a ≫ b) ≫ F.map (x + y) ≫ c ≫ d =
      ((a ≫ b) ≫ F.map x ≫ c ≫ d) + ((a ≫ b) ≫ F.map y ≫ c ≫ d) := by
  simp only [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]

private theorem five_factor_zero
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] {X Y : C} {P Q R T : D}
    (a : P ⟶ Q) (b : Q ⟶ F.obj X) (c : F.obj Y ⟶ R) (d : R ⟶ T) :
    (a ≫ b) ≫ F.map (0 : X ⟶ Y) ≫ c ≫ d = 0 := by
  simp only [Functor.map_zero, Limits.comp_zero, Limits.zero_comp]
```

## Users

Claims were rechecked read-only against the live project at 22:30 +08 on 2026-10-14. This item is held by W4; the coefficient-square module and every other listed prerequisite and adapter are unclaimed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawDiagram | unclaimed | Group the source pair in private add/zero lemmas so they match the refactored map. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackIdentity | unclaimed | Normalize the expanded raw map by Category.assoc before applying the existing generic theorem. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawTriangleAdjunct | unclaimed | Prove the normalized raw-map equality locally, then apply the existing generic adjunct theorem directly. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawTrianglePullback | unclaimed | Share the source pair; unfold it and normalize associativity in naturality. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawTrianglePullbackComposition | unclaimed | Unfold rawTriangleSource with rawTriangleMap in the existing generic proof. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomSourceFormula | unclaimed | Same maps and public signatures via canonical re-export; original source checked against the delivered overlay. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomTargetFormula | unclaimed | Same maps and public signatures via canonical re-export; original source checked against the delivered overlay. |
| Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientFactors | unclaimed | New canonical home for the same two module and abelian coefficient definitions; no new proof obligation. |
| Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientSquare | unclaimed | Remove the relocated module and abelian definitions and publicly re-export their canonical home; scalarCoefficientFactor, proofs and theorem signatures stay identical. |
| Sheaf.AlgebraicGeometry.RawModuleScalarHomCompositeFormula | unclaimed | Same maps and public signatures via canonical re-export; original source checked against the delivered overlay. |
| Sheaf.AlgebraicGeometry.RawModuleScalarHomEvaluation | unclaimed | Same maps and public signatures via canonical re-export; original source checked against the delivered overlay. |
| Sheaf.AlgebraicGeometry.RawModuleScalarPullbackAbelianFormula | unclaimed | Same maps and public signatures via canonical re-export; original source checked against the delivered overlay. |
| Sheaf.AlgebraicGeometry.RawModuleScalarPullbackFormulas | unclaimed | Same maps and public signatures via canonical re-export; original source checked against the delivered overlay. |
| Sheaf.AlgebraicGeometry.RawModuleScalarPullbackModuleFormula | W4 | Unchanged theorem proved by rfl; import canonical definitions instead of coefficient-square theorem. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSourceClassFormula | unclaimed | Same maps and public signatures via canonical re-export; original source checked against the delivered overlay. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSourceFactors | unclaimed | Use the exact generic source construction and directly publicly import its module; all public signatures stay identical. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSourceSquare | unclaimed | Same maps and public signatures via canonical re-export; original source checked against the delivered overlay. |

The changed raw map is extensionally the same composite for every class, including zero, identity arrows, negative shifts and zero coefficients. The target statements in `lean/Challenge.lean` are unchanged. The maintainer should record the definition review for any target whose import closure uses these maps and verify the set in the global build.

After the landing-conflict repair, all thirteen current original client sources selected by changed-factor uses and raw-triangle dependencies compiled against the delivered overlay without source changes, with no errors or warnings and below 60 seconds each. The parent conjunction was rebuilt and its axiom print, together with the module and abelian formulas, contains only the three permitted axioms. The generic equality between the old and regrouped rawTriangleMap expressions compiled using Category.assoc. The original module source and coefficient expressions equal the new ones by rfl. Fresh axiom prints for both retained coefficient-square theorems also show only propext, Classical.choice, and Quot.sound.

## Status

landed 20261014T164643-L-2302992 2026-10-14 (merge of deliver/W4/Sheaf.AlgebraicGeometry.RawModuleScalarPullbackModuleFormula)
