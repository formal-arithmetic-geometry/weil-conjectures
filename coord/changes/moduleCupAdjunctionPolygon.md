# moduleCup_adjunction_polygon

## Reason

The theorem's hQ equation `qLax = inferInstance` resolves the instance to qLax itself:
a scratch copy compiled with `guard_hyp hQ : qLax = qLax`. It therefore did not express
the canonical normalization required by the natural-language node and Stacks Tag 0FP3.
Replace its right side by the explicit `DerivedCategory.laxMonoidalQ` instance. This is a
statement correction, not a proof of the original arbitrary-structure statement; closing
the original hole by this correction is not claimed as progress.

Every other existing hypothesis and the conclusion are unchanged. All original local
instance declarations and the theorem docstring are preserved. The new cochain comparison
is constructed from specified localization isomorphisms and α; no witness is chosen.
The proof then uses the proved ordinary cochain evaluation identity and proved categorical
calculation, leaving only the strictly smaller quotient-transport theorem open.

The repository refreshed during the reading: the main module now exists, with one sorry;
the three helper modules are new. `tools/downstream.py --uses` lists 195 downstream
modules and only ModuleCupKInjectiveTarget uses the theorem. Its supplied cupSourceLax is
the canonical instance, so its normalization proof remains rfl. The original caller was
compiled against the delivery overlay and needs no adaptation. All other downstream
modules use unchanged caller statements, so no statement or definition changes there.
No Challenge target or definition used by a target is changed; no target review reopens.

## Old

The main theorem's exact old signature is:

```lean
theorem moduleCup_adjunction_polygon
    (qLax :
      (DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).LaxMonoidal)
    (hQ : qLax = (inferInstance :
      (DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).LaxMonoidal))
    (β : (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor)
    (hβ : β =
      (Functor.isoWhiskerLeft
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℤ))
        (DerivedCategory.quotientCompQhIso
          (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))))).inv ≫
        Functor.whiskerLeft (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctorUnit ≫
        (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor).hom)
    (P : ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace))
    [P.Additive] [P.Monoidal] [P.IsLeftAdjoint]
    (adj : P ⊣ RingedSpace.globalSectionsFunctor X.toRingedSpace)
    (D : DerivedCategory
        (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (α : DerivedCategory.Qh ⋙ D ⟶
      P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (dAdj : D ⊣ (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor)
    (δ : ∀ A B, D.obj (A ⊗ B) ≅ D.obj A ⊗ D.obj B)
    (hNat : ∀ A A' B B' (f : A ⟶ A') (g : B ⟶ B'),
      D.map (f ⊗ₘ g) ≫ (δ A' B').hom =
        (δ A B).hom ≫ (D.map f ⊗ₘ D.map g))
    (hTensor : ∀ K M, moduleCup_globalTensorDiagram X P D α δ K M)
    (hCounit : ∀ K : HomotopyCategory
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ),
      D.map ((RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctorUnit.app K) ≫
        dAdj.counit.app (DerivedCategory.Qh.obj K) =
      α.app (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map ((adj.mapHomotopyCategory (ComplexShape.up ℤ)).counit.app K))
    (hOrdinary : ∀ M N : SheafOfModules.{u} (moduleRings X.toRingedSpace),
      Functor.LaxMonoidal.μ P
          ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj M)
          ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj N) ≫
        P.map (moduleCup_sectionTensorMap X M N) ≫ adj.counit.app (M ⊗ N) =
          adj.counit.app M ⊗ₘ adj.counit.app N)
    (μ : ∀ A B : DerivedCategory
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)),
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj A ⊗
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj B ⟶
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj (A ⊗ B))
    (hμ : μ = fun A B ↦
      dAdj.homEquiv
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj A ⊗
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj B)
        (A ⊗ B)
        ((δ ((RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj A)
          ((RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj B)).hom ≫
          (dAdj.counit.app A ⊗ₘ dAdj.counit.app B))) :
    letI := qLax
    let S := RingedSpace.globalSectionsFunctor X.toRingedSpace
    let T := S.mapHomologicalComplex (ComplexShape.up ℤ)
    let R := S.rightDerivedFunctor
    ∀ (K L I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
      [I.IsKInjective] (φ : K ⊗ L ⟶ I),
      (β.app K ⊗ₘ β.app L) ≫ μ (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) ≫
        R.map (Functor.LaxMonoidal.μ DerivedCategory.Q K L ≫ DerivedCategory.Q.map φ) =
      Functor.LaxMonoidal.μ DerivedCategory.Q (T.obj K) (T.obj L) ≫
        DerivedCategory.Q.map (moduleCup_naiveMap X K L ≫ T.map φ) ≫ β.app I
```

The three helper modules and their declarations were absent.

## New

The exact new signatures and the constructed definition are:

```lean
noncomputable def moduleCup_cochainPullbackComparison
    (P : ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace)) [P.Additive]
    (D : DerivedCategory
        (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (α : DerivedCategory.Qh ⋙ D ⟶
      P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :
    DerivedCategory.Q ⋙ D ⟶
      P.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso
    (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))) D).inv ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ (ComplexShape.up ℤ)) α ≫
    (Functor.isoWhiskerLeft (P.mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)))).hom

theorem moduleCup_adjunction_polygon
    (qLax :
      (DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).LaxMonoidal)
    (hQ : qLax = DerivedCategory.laxMonoidalQ
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (β : (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor)
    (hβ : β =
      (Functor.isoWhiskerLeft
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℤ))
        (DerivedCategory.quotientCompQhIso
          (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))))).inv ≫
        Functor.whiskerLeft (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctorUnit ≫
        (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor).hom)
    (P : ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace))
    [P.Additive] [P.Monoidal] [P.IsLeftAdjoint]
    (adj : P ⊣ RingedSpace.globalSectionsFunctor X.toRingedSpace)
    (D : DerivedCategory
        (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (α : DerivedCategory.Qh ⋙ D ⟶
      P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (dAdj : D ⊣ (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor)
    (δ : ∀ A B, D.obj (A ⊗ B) ≅ D.obj A ⊗ D.obj B)
    (hNat : ∀ A A' B B' (f : A ⟶ A') (g : B ⟶ B'),
      D.map (f ⊗ₘ g) ≫ (δ A' B').hom =
        (δ A B).hom ≫ (D.map f ⊗ₘ D.map g))
    (hTensor : ∀ K M, moduleCup_globalTensorDiagram X P D α δ K M)
    (hCounit : ∀ K : HomotopyCategory
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ),
      D.map ((RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctorUnit.app K) ≫
        dAdj.counit.app (DerivedCategory.Qh.obj K) =
      α.app (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map ((adj.mapHomotopyCategory (ComplexShape.up ℤ)).counit.app K))
    (hOrdinary : ∀ M N : SheafOfModules.{u} (moduleRings X.toRingedSpace),
      Functor.LaxMonoidal.μ P
          ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj M)
          ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj N) ≫
        P.map (moduleCup_sectionTensorMap X M N) ≫ adj.counit.app (M ⊗ N) =
          adj.counit.app M ⊗ₘ adj.counit.app N)
    (μ : ∀ A B : DerivedCategory
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)),
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj A ⊗
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj B ⟶
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj (A ⊗ B))
    (hμ : μ = fun A B ↦
      dAdj.homEquiv
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj A ⊗
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj B)
        (A ⊗ B)
        ((δ ((RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj A)
          ((RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj B)).hom ≫
          (dAdj.counit.app A ⊗ₘ dAdj.counit.app B))) :
    letI := qLax
    let S := RingedSpace.globalSectionsFunctor X.toRingedSpace
    let T := S.mapHomologicalComplex (ComplexShape.up ℤ)
    let R := S.rightDerivedFunctor
    ∀ (K L I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
      [I.IsKInjective] (φ : K ⊗ L ⟶ I),
      (β.app K ⊗ₘ β.app L) ≫ μ (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) ≫
        R.map (Functor.LaxMonoidal.μ DerivedCategory.Q K L ≫ DerivedCategory.Q.map φ) =
      Functor.LaxMonoidal.μ DerivedCategory.Q (T.obj K) (T.obj L) ≫
        DerivedCategory.Q.map (moduleCup_naiveMap X K L ≫ T.map φ) ≫ β.app I

theorem moduleCup_cochain_comparison_squares
    (qLax :
      (DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).LaxMonoidal)
    (hQ : qLax = DerivedCategory.laxMonoidalQ
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (β : (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor)
    (hβ : β =
      (Functor.isoWhiskerLeft
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℤ))
        (DerivedCategory.quotientCompQhIso
          (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))))).inv ≫
        Functor.whiskerLeft (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctorUnit ≫
        (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor).hom)
    (P : ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace))
    [P.Additive] [P.Monoidal] [P.IsLeftAdjoint]
    (adj : P ⊣ RingedSpace.globalSectionsFunctor X.toRingedSpace)
    (D : DerivedCategory
        (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (α : DerivedCategory.Qh ⋙ D ⟶
      P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (dAdj : D ⊣ (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor)
    (δ : ∀ A B, D.obj (A ⊗ B) ≅ D.obj A ⊗ D.obj B)
    (hTensor : ∀ K M, moduleCup_globalTensorDiagram X P D α δ K M)
    (hCounit : ∀ K : HomotopyCategory
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ),
      D.map ((RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctorUnit.app K) ≫
        dAdj.counit.app (DerivedCategory.Qh.obj K) =
      α.app (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map ((adj.mapHomotopyCategory (ComplexShape.up ℤ)).counit.app K)) :
    letI := qLax
    let Q := DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let Q₀ := DerivedCategory.Q
      (C := ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
    let F := P.mapHomologicalComplex (ComplexShape.up ℤ)
    let a := moduleCup_cochainPullbackComparison X P D α
    let T := (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℤ)
    (∀ A B, D.map (Functor.LaxMonoidal.μ Q₀ A B) ≫ a.app (A ⊗ B) ≫
        Q.map (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans
          (ComplexShape.up ℤ) P).app A).app B) =
      (δ (Q₀.obj A) (Q₀.obj B)).hom ≫ (a.app A ⊗ₘ a.app B) ≫
        Functor.LaxMonoidal.μ Q (F.obj A) (F.obj B)) ∧
    (∀ K, D.map (β.app K) ≫
        dAdj.counit.app (Q.obj K) =
      a.app (T.obj K) ≫ Q.map
        ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app K))

theorem moduleCup_cochain_counit_tensor
    (P : ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace))
    [P.Additive] [P.Monoidal] [P.IsLeftAdjoint]
    (adj : P ⊣ RingedSpace.globalSectionsFunctor X.toRingedSpace)
    (hOrdinary : ∀ M N : SheafOfModules.{u} (moduleRings X.toRingedSpace),
      Functor.LaxMonoidal.μ P
          ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj M)
          ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj N) ≫
        P.map (moduleCup_sectionTensorMap X M N) ≫ adj.counit.app (M ⊗ N) =
          adj.counit.app M ⊗ₘ adj.counit.app N)
    (K L : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let T := (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℤ)
    let F := P.mapHomologicalComplex (ComplexShape.up ℤ)
    F.map (moduleCup_naiveMap X K L) ≫
        (adj.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app (K ⊗ L) =
      ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans
        (ComplexShape.up ℤ) P).app (T.obj K)).app (T.obj L) ≫
        ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app K ⊗ₘ
          (adj.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app L)

theorem moduleCup_polygon_calculation
    {C C₀ E E₀ : Type*} [Category* C] [Category* C₀] [Category* E] [Category* E₀]
    [MonoidalCategory C] [MonoidalCategory C₀]
    [MonoidalCategory E] [MonoidalCategory E₀]
    (Q : C ⥤ E) [Q.LaxMonoidal] (Q₀ : C₀ ⥤ E₀) [Q₀.LaxMonoidal]
    (T : C ⥤ C₀) (F : C₀ ⥤ C) (D : E₀ ⥤ E) (R : E ⥤ E₀)
    (adj : F ⊣ T) (dAdj : D ⊣ R)
    (a : Q₀ ⋙ D ⟶ F ⋙ Q) (b : T ⋙ Q₀ ⟶ Q ⋙ R)
    (δ : ∀ A B, D.obj (A ⊗ B) ≅ D.obj A ⊗ D.obj B)
    (hNat : ∀ A A' B B' (f : A ⟶ A') (g : B ⟶ B'),
      D.map (f ⊗ₘ g) ≫ (δ A' B').hom =
        (δ A B).hom ≫ (D.map f ⊗ₘ D.map g))
    (t : ∀ A B, F.obj (A ⊗ B) ⟶ F.obj A ⊗ F.obj B)
    (ht : ∀ A B, D.map (Functor.LaxMonoidal.μ Q₀ A B) ≫ a.app (A ⊗ B) ≫
      Q.map (t A B) = (δ (Q₀.obj A) (Q₀.obj B)).hom ≫
        (a.app A ⊗ₘ a.app B) ≫ Functor.LaxMonoidal.μ Q (F.obj A) (F.obj B))
    (hc : ∀ K, D.map (b.app K) ≫ dAdj.counit.app (Q.obj K) =
      a.app (T.obj K) ≫ Q.map (adj.counit.app K))
    (K L I : C) (m : T.obj K ⊗ T.obj L ⟶ T.obj (K ⊗ L))
    (ho : F.map m ≫ adj.counit.app (K ⊗ L) =
      t (T.obj K) (T.obj L) ≫ (adj.counit.app K ⊗ₘ adj.counit.app L))
    (φ : K ⊗ L ⟶ I) :
    (b.app K ⊗ₘ b.app L) ≫
      dAdj.homEquiv _ _ ((δ _ _).hom ≫
        (dAdj.counit.app (Q.obj K) ⊗ₘ dAdj.counit.app (Q.obj L))) ≫
      R.map (Functor.LaxMonoidal.μ Q K L ≫ Q.map φ) =
    Functor.LaxMonoidal.μ Q₀ (T.obj K) (T.obj L) ≫ Q₀.map (m ≫ T.map φ) ≫
      b.app I
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ModuleCupAdjunctionPolygon | Q2 | Canonical-instance hypothesis corrected; other existing signatures preserved. |
| Sheaf.Paper.ModuleCupAdjunctionCalculation | Q2 | New module; proved categorical calculation. |
| Sheaf.Paper.ModuleCupCochainCounitTensor | Q2 | New module; proved ordinary cochain evaluation. |
| Sheaf.Paper.ModuleCupCochainComparisonSquares | Q2 | New module; explicit comparison and open quotient transport. |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | N2 | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegree | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardExternalCechCupComponent | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardExternalCechCupDifferential | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardExternalCechCupDifferentialCoordinate | XR32ae8835ad92617e | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardExternalCechCupLeibniz | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardExternalCechCupNaturality | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftCechComparison | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftCechGenerators | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftComparisonComplexes | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftHomologyLadder | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardExternalCupQuasiIso | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardExternalCupRightCechDiagram | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardExternalCupRightExactLadder | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardExternalCupRightShortExact | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardExternalCupShiftLeft | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardExternalCupShiftRight | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardExternalRightCechComparison | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardH1ProductInjective | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardH1ProductSpanning | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardKunnethCechModels | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcoh | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcohIso | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardLeftCechCupComponent | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardLeftCechCupConstruction | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardLeftCechCupHomology | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardLeftCechCupNaturality | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardLeftRightCechCup | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardRightCechCupConstruction | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardRightCechCupCycleComparison | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardRightCechCupGenerators | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardRightCechCupHomology | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardScalarCechExternalCup | U4 | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ProductResidueH1Injective | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.Paper.CechCupProduct | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.Paper.CechCupPullbackCompat | W2 | Transitive dependency only; no statement or definition changes. |
| Sheaf.Paper.CechCupResolutionRepresentatives | XRb34b66c78de005d0 | Transitive dependency only; no statement or definition changes. |
| Sheaf.Paper.ModuleCohomologyCupProduct | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.Paper.ModuleCupEqualDerivedMapsClass | Q3 | Transitive dependency only; no statement or definition changes. |
| Sheaf.Paper.ModuleCupKInjectiveTarget | unclaimed | Supplies the canonical lax instance; original compiles unchanged against delivery. |
| Sheaf.Paper.ModuleCupNaiveDerivedCompatibility | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.Paper.ModuleCupRealizationEvaluation | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.Paper.ModuleCupResolutionInvariance | unclaimed | Transitive dependency only; no statement or definition changes. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Transitive dependency only; no statement or definition changes. |
| TargetsCheck | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Transitive dependency only; no statement or definition changes. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Transitive dependency only; no statement or definition changes. |

No forced adaptations are delivered.

## Status

landed 20261014T013043-L-3416738 2026-10-14 (merge of deliver/Q2/Sheaf.Paper.ModuleCupAdjunctionPolygon)
