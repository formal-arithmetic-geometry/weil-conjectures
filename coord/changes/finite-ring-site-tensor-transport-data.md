# AlgebraicGeometry.ProEtale.finiteRingSiteTensorTranspose shared interface

## Reason

The two new canonical-map lemmas and the categorical assembly theorem need the existing
transport definitions in their signatures. Keeping those definitions in the item would create
an import cycle. Move the definitions unchanged into FiniteRingSiteTensorTransposeData and
publicly import it from the original item. This is a dependency extraction, not a mathematical
repair or a response to a compile timeout. No source-library module is changed.

## Old

In lean/Sheaf/AlgebraicGeometry/FiniteRingSiteTensorTranspose.lean:

```lean
/-- Exact, termwise site inverse image. Source: blueprint, assertion 1
(blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
abbrev finiteRingSitePull (B : Type) [CommRing B] [Finite B] (T : Scheme.{u}) :=
  (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) T).mapDerivedCategory

/-- Canonical tensor comparison, transported from the left derived functor to the
termwise exact inverse image. Its K-flat normalization is the ordinary pure-tensor map.
Source: blueprint proof step 5; Stacks 07A4
(blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
@[irreducible] def finiteRingSiteTensor
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (T : Scheme.{u}) [(comparisonUpperStar A T).PreservesFlat]
    (M N : DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    (comparisonUpperStar A T).mapDerivedCategory.obj (M ⊗ N) ≅
      (comparisonUpperStar A T).mapDerivedCategory.obj M ⊗
        (comparisonUpperStar A T).mapDerivedCategory.obj N :=
  (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso A M).app N

/-- The unit comparison is the image of the ordinary constant-ring unit comparison.
Source: blueprint proof step 5; Stacks 07A4
(blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
@[irreducible] def finiteRingSiteUnit (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (T : Scheme.{u}) :
    (comparisonUpperStar A T).mapDerivedCategory.obj (𝟙_ _) ≅ 𝟙_ _ :=
  ((comparisonUpperStar A T).mapDerivedCategoryFactors).app _ ≪≫
  DerivedCategory.Q.mapIso
    (((HomologicalComplex.singleMapHomologicalComplex
      (comparisonUpperStar A T) (.up ℤ) 0).app _) ≪≫
    (HomologicalComplex.single _ (.up ℤ) 0).mapIso
      (Functor.Monoidal.εIso
        (comparisonUpperStar A T)).symm)

/-- The pullback identification with the derived inverse images used by the projection maps.
Source: blueprint proof step 5; the exact/left-derived identifications are canonical
(blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
@[irreducible] def finiteRingSitePullback
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (square : (comparisonUpperStar A Y).mapDerivedCategory ⋙
      (upperStar A f).mapDerivedCategory ≅
        (Etale.upperStar A f).mapDerivedCategory ⋙ (comparisonUpperStar A X).mapDerivedCategory)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (comparisonUpperStar A X).mapDerivedCategory.obj
        ((Etale.upperStar A f).leftDerivedFunctor.obj K) ≅
      (upperStar A f).leftDerivedFunctor.obj
        ((comparisonUpperStar A Y).mapDerivedCategory.obj K) :=
  (comparisonUpperStar A X).mapDerivedCategory.mapIso
    ((Etale.upperStar A f).leftDerivedFunctorIsoMapDerivedCategory.app K) ≪≫
  square.symm.app K ≪≫
  ((upperStar A f).leftDerivedFunctorIsoMapDerivedCategory.app
    ((comparisonUpperStar A Y).mapDerivedCategory.obj K)).symm

/-- Ordinary etale compact supports for the fixed compactification.
Source: blueprint assertion 1 (blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
abbrev finiteRingEtaleShriek (B : Type) [CommRing B] {X Y : Scheme.{u}}
    {f : X ⟶ Y} (c : Compactification f) :=
  Etale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1} B)) c

/-- Ordinary pro-etale compact supports before restriction to the localizing closure.
Source: blueprint assertion 1 (blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
abbrev finiteRingProShriek (B : Type) [CommRing B] {X Y : Scheme.{u}}
    {f : X ⟶ Y} (c : Compactification f) :=
  rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1} B)) c

/-- The canonical etale projection-map component, with abstract coefficients.
Source: blueprint assertion 2 (blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
@[irreducible] def finiteRingEtalePF
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [Etale.UpperStarPreservesFlat A]
    {FC : A → A → Type v} {CC : A → Type (u + 1)}
    [∀ P Q : A, FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (Etale.rightDerivedLowerShriekOfCompactification A c).obj M ⊗ K ⟶
      (Etale.rightDerivedLowerShriekOfCompactification A c).obj
        (M ⊗ (Etale.upperStar A f).leftDerivedFunctor.obj K) :=
  ((Etale.projectionMapOfCompactification A c).app M).app K

/-- The canonical pro-etale projection-map component, with abstract coefficients.
Source: blueprint assertion 2 (blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
@[irreducible] def finiteRingProPF
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    (rightDerivedLowerShriekOfCompactification A c).obj M ⊗ K ⟶
      (rightDerivedLowerShriekOfCompactification A c).obj
        (M ⊗ (upperStar A f).leftDerivedFunctor.obj K) :=
  ((projectionMapOfCompactification A c).app M).app K

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

/-- Restriction of a functor to the indicated full subcategories.
Source: blueprint assertion 1 (blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
abbrev finiteRingRestriction
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (P : ObjectProperty C) (Q : ObjectProperty D)
    (h : ∀ N, P N → Q (F.obj N)) :=
  Q.lift (P.ι ⋙ F) (fun N ↦ h N.obj N.property)

/-- Restriction of the codomain of the exact site comparison to its image.
Source: blueprint assertion 1 (blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
abbrev finiteRingImageLift
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (E : C ⥤ D) (P : ObjectProperty D) (h : ∀ M, P (E.obj M)) :=
  P.lift E h

/-- The composite tensor and pullback comparison, retaining its specified two factors.
Source: blueprint proof step 5 (blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
def finiteRingTensorPullbackComparison
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {D : Type u₂} [Category.{v₂} D]
    {C' : Type u₃} [Category.{v₃} C'] [MonoidalCategory C']
    {D' : Type u₄} [Category.{v₄} D']
    (E : C ⥤ C') (P : D ⥤ C) (P' : D' ⥤ C') (E' : D ⥤ D')
    (tensor : ∀ M N, E.obj (M ⊗ N) ≅ E.obj M ⊗ E.obj N)
    (pullback : ∀ K, E.obj (P.obj K) ≅ P'.obj (E'.obj K))
    (M : C) (K : D) :
    E.obj (M ⊗ P.obj K) ≅ E.obj M ⊗ P'.obj (E'.obj K) :=
  tensor M (P.obj K) ≪≫ tensorIso (Iso.refl _) (pullback K)

/-- The three categorical assertions of finite-ring site transport, with the categories
and the specified maps kept abstract to avoid expanding K-flat constructions at each use.
The main theorem specializes every argument to its recorded canonical construction.
Source: blueprint assertions 1--3
(blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
def finiteRingSiteTensorTransposeStatement
    {EXCat : Type u₁} [Category.{v₁} EXCat] [MonoidalCategory EXCat]
    {EYCat : Type u₂} [Category.{v₂} EYCat] [MonoidalCategory EYCat]
    {PXCat : Type u₃} [Category.{v₃} PXCat] [MonoidalCategory PXCat]
    {PYCat : Type u₄} [Category.{v₄} PYCat] [MonoidalCategory PYCat]
    (EX : EXCat ⥤ PXCat) (EY : EYCat ⥤ PYCat)
    (FE : EXCat ⥤ EYCat) (FP : PXCat ⥤ PYCat)
    (PE : EYCat ⥤ EXCat) (PP : PYCat ⥤ PXCat)
    (PX : ObjectProperty PXCat) (PY : ObjectProperty PYCat)
    (beta : ∀ M, EY.obj (FE.obj M) ⟶ FP.obj (EX.obj M))
    (tensorX : ∀ M N, EX.obj (M ⊗ N) ≅ EX.obj M ⊗ EX.obj N)
    (tensorY : ∀ M N, EY.obj (M ⊗ N) ≅ EY.obj M ⊗ EY.obj N)
    (unitY : EY.obj (𝟙_ EYCat) ≅ 𝟙_ PYCat)
    (pullback : ∀ K, EX.obj (PE.obj K) ≅ PP.obj (EY.obj K))
    (symE : BraidedCategory EXCat)
    (symP : BraidedCategory PXCat)
    (pfE : ∀ M K, FE.obj M ⊗ K ⟶ FE.obj (M ⊗ PE.obj K))
    (pfP : ∀ M K, FP.obj M ⊗ K ⟶ FP.obj (M ⊗ PP.obj K)) : Prop :=
    (EX).Full ∧ (EX).Faithful ∧
    (∀ N, (EX).essImage N ↔ PX N) ∧
    ∃ (hX : ∀ M, PX ((EX).obj M))
      (hY : ∀ K, PY ((EY).obj K))
      (b : FE ⋙ EY ≅
        EX ⋙ FP),
      (∀ M, b.hom.app M = beta M) ∧
      ∀ (hs : ∀ N, PX N →
          PY ((FP).obj N))
        (R : EYCat ⥤
          EXCat)
        (ae : FE ⊣ R)
        (G : (PY).FullSubcategory ⥤
          (PX).FullSubcategory)
        (ap : finiteRingRestriction FP PX PY hs ⊣ G),
        ∃ (rho : R ⋙ finiteRingImageLift EX PX hX ≅ finiteRingImageLift EY PY hY ⋙ G),
          (∀ L, b.hom.app (R.obj L) ≫
              (FP).map (rho.hom.app L).hom ≫
              (ap.counit.app ((finiteRingImageLift EY PY hY).obj L)).hom =
            (EY).map (ae.counit.app L)) ∧
          (∀ sigma : R ⋙ finiteRingImageLift EX PX hX ≅
              finiteRingImageLift EY PY hY ⋙ G,
            (∀ L, b.hom.app (R.obj L) ≫
                (FP).map (sigma.hom.app L).hom ≫
                (ap.counit.app ((finiteRingImageLift EY PY hY).obj L)).hom =
              (EY).map (ae.counit.app L)) → sigma = rho) ∧
          ∃ (pe : ∀ M K, (FE).obj M ⊗ K ≅
              (FE).obj ((M ⊗ PE.obj K)))
            (pp : ∀ M K, (FP).obj ((EX).obj M) ⊗
                (EY).obj K ≅
              (FP).obj ((EX.obj M ⊗ PP.obj (EY.obj K))))
            (ht : ∀ M K,
              PX ((EX.obj M ⊗ PP.obj (EY.obj K)))),
            (∀ M K, (pe M K).hom =
              pfE M K) ∧
            (∀ M K, (pp M K).hom =
              pfP (EX.obj M) (EY.obj K)) ∧
            (∀ M K,
              (EY).map
                  (pfE M K) ≫
                  b.hom.app ((M ⊗ PE.obj K)) ≫
                  (FP).map
                    (finiteRingTensorPullbackComparison EX PE PP EY tensorX pullback M K).hom =
                (tensorY (FE.obj M) K).hom ≫
                  (b.hom.app M ⊗ₘ 𝟙 ((EY).obj K)) ≫
                  pfP (EX.obj M) (EY.obj K)) ∧
            (∀ (M : EXCat)
              (K : EYCat)
              (e : (FE).obj M ⟶ 𝟙_ _),
              (EX).map
                  (ae.homEquiv _ _ ((pe M K).inv ≫ (e ⊗ₘ 𝟙 K) ≫ (λ_ K).hom)) ≫
                  (rho.hom.app K).hom =
                (finiteRingTensorPullbackComparison EX PE PP EY tensorX pullback M K).hom ≫
                  (ap.homEquiv ⟨(EX.obj M ⊗ PP.obj (EY.obj K)), ht M K⟩
                    ((finiteRingImageLift EY PY hY).obj K)
                    (ObjectProperty.homMk ((pp M K).inv ≫
                      (((b.app M).inv ≫ (EY).map e ≫
                        (unitY).hom) ⊗ₘ
                          𝟙 ((EY).obj K)) ≫
                      (λ_ ((EY).obj K)).hom))).hom) ∧
            (∀ (M : EXCat)
              (K : EYCat)
              (e : (FE).obj M ⟶ 𝟙_ _),
              (EX).map
                  ((@BraidedCategory.braiding EXCat _ _ symE (PE.obj K) M).hom ≫
                    ae.homEquiv _ _ ((pe M K).inv ≫ (e ⊗ₘ 𝟙 K) ≫ (λ_ K).hom)) ≫
                  (rho.hom.app K).hom =
                (tensorX (PE.obj K) M).hom ≫
                  ((pullback K).hom ⊗ₘ
                    𝟙 ((EX).obj M)) ≫
                  (@BraidedCategory.braiding PXCat _ _ symP (PP.obj (EY.obj K)) (EX.obj M)).hom ≫
                  (ap.homEquiv ⟨(EX.obj M ⊗ PP.obj (EY.obj K)), ht M K⟩
                    ((finiteRingImageLift EY PY hY).obj K)
                    (ObjectProperty.homMk ((pp M K).inv ≫
                      (((b.app M).inv ≫ (EY).map e ≫
                        (unitY).hom) ⊗ₘ
                          𝟙 ((EY).obj K)) ≫
                      (λ_ ((EY).obj K)).hom))).hom)

/-- The categorical transport formulas applied to the actual six site functors.
Keeping this partial application named shares the derived-category instance data.
Source: blueprint assertions 1--3
(blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
@[irreducible] def finiteRingSiteTensorTransposeSiteFunctors
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [Etale.UpperStarPreservesFlat A] [UpperStarPreservesFlat A]
    {FC : A → A → Type v} {CC : A → Type (u + 1)}
    [∀ P Q : A, FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ T : Scheme.{u}, T.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  finiteRingSiteTensorTransposeStatement
    (comparisonUpperStar A X).mapDerivedCategory
    (comparisonUpperStar A Y).mapDerivedCategory
    (Etale.rightDerivedLowerShriekOfCompactification A c)
    (rightDerivedLowerShriekOfCompactification A c)
    (Etale.upperStar A f).leftDerivedFunctor (upperStar A f).leftDerivedFunctor

/-- The site transport assertion with its canonical tensor, unit and pullback maps.
Source: blueprint proof step 5 (blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
@[irreducible] def finiteRingSiteTensorTransposeCanonicalTensor
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [Etale.UpperStarPreservesFlat A] [UpperStarPreservesFlat A]
    {FC : A → A → Type v} {CC : A → Type (u + 1)}
    [∀ P Q : A, FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ T : Scheme.{u}, T.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    [(comparisonUpperStar A X).PreservesFlat] [(comparisonUpperStar A Y).PreservesFlat]
    (PX : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)))
    (PY : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)))
    (beta : ∀ M, (comparisonUpperStar A Y).mapDerivedCategory.obj
        ((Etale.rightDerivedLowerShriekOfCompactification A c).obj M) ⟶
      (rightDerivedLowerShriekOfCompactification A c).obj
        ((comparisonUpperStar A X).mapDerivedCategory.obj M))
    (square : (comparisonUpperStar A Y).mapDerivedCategory ⋙
      (upperStar A f).mapDerivedCategory ≅
        (Etale.upperStar A f).mapDerivedCategory ⋙ (comparisonUpperStar A X).mapDerivedCategory) :=
  finiteRingSiteTensorTransposeSiteFunctors A c
    PX PY beta (finiteRingSiteTensor A X) (finiteRingSiteTensor A Y)
    (finiteRingSiteUnit A Y) (finiteRingSitePullback A f square)

/-- The site transport assertion with the canonical signed symmetries on both sites.
Source: blueprint proof step 11 (blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
@[irreducible] def finiteRingSiteTensorTransposeCanonicalSymmetry
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [Etale.UpperStarPreservesFlat A] [UpperStarPreservesFlat A]
    {FC : A → A → Type v} {CC : A → Type (u + 1)}
    [∀ P Q : A, FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ T : Scheme.{u}, T.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    [(comparisonUpperStar A X).PreservesFlat] [(comparisonUpperStar A Y).PreservesFlat]
    (PX : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)))
    (PY : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)))
    (beta : ∀ M, (comparisonUpperStar A Y).mapDerivedCategory.obj
        ((Etale.rightDerivedLowerShriekOfCompactification A c).obj M) ⟶
      (rightDerivedLowerShriekOfCompactification A c).obj
        ((comparisonUpperStar A X).mapDerivedCategory.obj M))
    (square : (comparisonUpperStar A Y).mapDerivedCategory ⋙
      (upperStar A f).mapDerivedCategory ≅
        (Etale.upperStar A f).mapDerivedCategory ⋙ (comparisonUpperStar A X).mapDerivedCategory) :=
  finiteRingSiteTensorTransposeCanonicalTensor A c PX PY beta square
    (DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology A))
    (DerivedCategory.braidedCategory' (Sheaf (Scheme.ProEt.topology X) A))

/-- The specified site transport assertion with its coefficient category abstract.
Every tensor, pullback, unit and symmetry argument is its canonical construction;
only the two closure predicates and the recorded compact-support comparison vary here.
Source: blueprint assertions 1--3
(blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
def finiteRingSiteTensorTransposeWithCoefficients
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [Etale.UpperStarPreservesFlat A] [UpperStarPreservesFlat A]
    {FC : A → A → Type v} {CC : A → Type (u + 1)}
    [∀ P Q : A, FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ T : Scheme.{u}, T.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    [(comparisonUpperStar A X).PreservesFlat] [(comparisonUpperStar A Y).PreservesFlat]
    (PX : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)))
    (PY : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)))
    (beta : ∀ M, (comparisonUpperStar A Y).mapDerivedCategory.obj
        ((Etale.rightDerivedLowerShriekOfCompactification A c).obj M) ⟶
      (rightDerivedLowerShriekOfCompactification A c).obj
        ((comparisonUpperStar A X).mapDerivedCategory.obj M))
    (square : (comparisonUpperStar A Y).mapDerivedCategory ⋙
      (upperStar A f).mapDerivedCategory ≅
        (Etale.upperStar A f).mapDerivedCategory ⋙ (comparisonUpperStar A X).mapDerivedCategory) :
    Prop :=
  finiteRingSiteTensorTransposeCanonicalSymmetry A c PX PY beta square
    (finiteRingEtalePF A c) (finiteRingProPF A c)
```

## New

The exact same declaration block, including signatures, attributes, visibility, and bodies,
is in lean/Sheaf/AlgebraicGeometry/FiniteRingSiteTensorTransposeData.lean. The original module
replaces that block by this public import (all original public imports are retained):

```lean
public import Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTransposeData
```

Thus every constant and every target definition is definitionally unchanged. The new shared
module contains no holes. The original node keeps its theorem attachment; the new definition
node def-pur-finite-ring-site-tensor-transport-data attaches all relocated definitions.

## Users

Read-only tools/downstream.py lists these nine consumers. No consumer mentions the main
theorem outside its defining module. None needs adaptation: public re-export preserves every
name and every definition. There are no forced adaptations.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | None: original declarations are re-exported verbatim. No edit required. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | None: original declarations are re-exported verbatim. No edit required. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | None: original declarations are re-exported verbatim. No edit required. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | None: original declarations are re-exported verbatim. No edit required. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | B7 | None: original declarations are re-exported verbatim. No edit required. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | None: original declarations are re-exported verbatim. No edit required. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | None: original declarations are re-exported verbatim. No edit required. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | X2 | None: original declarations are re-exported verbatim. No edit required. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | None: original declarations are re-exported verbatim. No edit required. |

## Status

landed 20261025T123735-L-1895222 2026-10-25 (merge of deliver/S3/Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose)
