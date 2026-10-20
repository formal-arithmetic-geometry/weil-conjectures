# CategoryTheory.ringedFiniteFreeHomBaseChange_coordinates

## Reason

Repair reviewer C-fc7ec D1 at fc7ec3275: the unconstrained existential basis
and Hom isomorphisms allowed the conclusion to encode invertibility of the comparison.
Pin the basis components on every K-flat representative. Pin β by the expanded
`scalarHomRestrictedEvaluation` formula, using ordinary and derived scalar adjunctions
fixed by their unit and chain-transpose normalizations. The normalization is stated for
the supplied E, T and μ, so no arbitrary comparison between separate chosen models is hidden.
The new predicate is a concrete proposition, containing no chosen data and no `sorry`.

## Old

```lean
theorem ringedFiniteFreeHomBaseChange_coordinates
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S))]
    (d : ℕ) (e :
      (SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map φ)).obj
          (SheafOfModules.unit
            (SheafOfModules.derivedChangeRingIndependentCoefficients J S)) ≅
        SheafOfModules.free (R :=
          SheafOfModules.derivedChangeRingIndependentCoefficients J R)
            (ULift.{max c v r} (Fin d)))
    (E : SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R) ⥤ SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S))
      (h : ∀ M, E.obj M = SheafOfModules.changeOfRings φ M)
      (_hm : ∀ {M N : SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)} (f : M ⟶ N),
        E.map f = eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom φ M f ≫
          eqToHom (h N).symm)
      (_hE : E.Additive)
      (T : DerivedCategory (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ⥤
        DerivedCategory (SheafOfModules.{max c v r}
          (SheafOfModules.derivedChangeRingIndependentCoefficients J S)))
      (ε : DerivedCategory.Q ⋙ T ⟶
        E.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (_hT : T.IsLeftDerivedFunctor ε
        (HomologicalComplex.quasiIso (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) (ComplexShape.up ℤ)))
      (AR : WeilConjectures.CoefficientClosedStructure
        (derivedInternalHomOfUniverses.{c, v, r, w} J R))
      (AS : WeilConjectures.CoefficientClosedStructure
        (derivedInternalHomOfUniverses.{c, v, r, w} J S))
      (MR : WeilConjectures.CoefficientTensorModels.{r, c, v, w} J R AR)
      (MS : WeilConjectures.CoefficientTensorModels.{r, c, v, w} J S AS)
      (κ : WeilConjectures.coefficientTotalTensor.{r, c, v} J R ⋙
          E.mapHomologicalComplex (ComplexShape.up ℤ) ≅
        (E.mapHomologicalComplex (ComplexShape.up ℤ)).prod
          (E.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
            WeilConjectures.coefficientTotalTensor.{r, c, v} J S)
      (μ : AR.tensor ⋙ T ≅ T.prod T ⋙ AS.tensor)
    (hκ : (∀ (P Q : CochainComplex (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
        (p q : ℤ) (U : Cᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        ((κ.hom.app (P, Q)).f (p + q)).val.app U
          (ringedFiniteFreeScalarSection.{c, v, r} J φ E h
            (((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)).X (p + q))
            U 1 (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R
              P Q p q (p + q) rfl U x y)) =
        WeilConjectures.coefficientTensorGenerator.{r, c, v} J S
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) p q (p + q) rfl U
          (ringedFiniteFreeScalarSection.{c, v, r} J φ E h (P.X p) U 1 x)
          (ringedFiniteFreeScalarSection.{c, v, r} J φ E h (Q.X q) U 1 y)))
    (hcomp : (∀ (P Q : CochainComplex (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
        (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
        (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q),
        ∃ (hEP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
          (hEQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)),
          IsIso (ε.app P) ∧ IsIso (ε.app Q) ∧
          T.map ((MR.iso J R AR P Q hP hQ).hom) ≫
              μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
              AS.tensor.map (Prod.mkHom (ε.app P) (ε.app Q)) =
            ε.app ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≫
              DerivedCategory.Q.map (κ.hom.app (P, Q)) ≫
              (MS.iso J S AS _ _ hEP hEQ).hom)) :
    ∀ P Q : DerivedCategory (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)),
    ∃ (a : (⨁ fun _ : Fin d ↦
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P, Q)) ≅
      (SheafOfModules.scalarDerivedRestriction φ).obj
        (T.obj ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P, Q))))
      (aQ : (⨁ fun _ : Fin d ↦ Q) ≅
        (SheafOfModules.scalarDerivedRestriction φ).obj (T.obj Q))
      (β : (SheafOfModules.scalarDerivedRestriction φ).obj
        ((derivedInternalHomOfUniverses.{c, v, r, w} J S).obj (op (T.obj P), T.obj Q)) ≅
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
          (op P, (SheafOfModules.scalarDerivedRestriction φ).obj (T.obj Q))),
      ∀ i : Fin d,
        biproduct.ι _ i ≫ a.hom ≫
          (SheafOfModules.scalarDerivedRestriction φ).map
            (AS.transpose _ (T.obj P) (T.obj Q)
              (μ.inv.app
                ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P, Q), P) ≫
                T.map (AR.evaluation P Q))) ≫ β.hom =
          (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
            (Prod.mkHom (𝟙 (op P)) (biproduct.ι _ i ≫ aQ.hom))
```

## New

```lean
theorem ringedFiniteFreeHomBaseChange_coordinates
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S))]
    (d : ℕ) (e :
      (SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map φ)).obj
          (SheafOfModules.unit
            (SheafOfModules.derivedChangeRingIndependentCoefficients J S)) ≅
        SheafOfModules.free (R :=
          SheafOfModules.derivedChangeRingIndependentCoefficients J R)
            (ULift.{max c v r} (Fin d)))
    (E : SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R) ⥤ SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S))
      (h : ∀ M, E.obj M = SheafOfModules.changeOfRings φ M)
      (_hm : ∀ {M N : SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)} (f : M ⟶ N),
        E.map f = eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom φ M f ≫
          eqToHom (h N).symm)
      [_hE : E.Additive]
      (T : DerivedCategory (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ⥤
        DerivedCategory (SheafOfModules.{max c v r}
          (SheafOfModules.derivedChangeRingIndependentCoefficients J S)))
      (ε : DerivedCategory.Q ⋙ T ⟶
        E.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (_hT : T.IsLeftDerivedFunctor ε
        (HomologicalComplex.quasiIso (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) (ComplexShape.up ℤ)))
      (AR : WeilConjectures.CoefficientClosedStructure
        (derivedInternalHomOfUniverses.{c, v, r, w} J R))
      (AS : WeilConjectures.CoefficientClosedStructure
        (derivedInternalHomOfUniverses.{c, v, r, w} J S))
      (MR : WeilConjectures.CoefficientTensorModels.{r, c, v, w} J R AR)
      (MS : WeilConjectures.CoefficientTensorModels.{r, c, v, w} J S AS)
      (κ : WeilConjectures.coefficientTotalTensor.{r, c, v} J R ⋙
          E.mapHomologicalComplex (ComplexShape.up ℤ) ≅
        (E.mapHomologicalComplex (ComplexShape.up ℤ)).prod
          (E.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
            WeilConjectures.coefficientTotalTensor.{r, c, v} J S)
      (μ : AR.tensor ⋙ T ≅ T.prod T ⋙ AS.tensor)
    (hκ : (∀ (P Q : CochainComplex (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
        (p q : ℤ) (U : Cᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        ((κ.hom.app (P, Q)).f (p + q)).val.app U
          (ringedFiniteFreeScalarSection.{c, v, r} J φ E h
            (((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)).X (p + q))
            U 1 (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R
              P Q p q (p + q) rfl U x y)) =
        WeilConjectures.coefficientTensorGenerator.{r, c, v} J S
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) p q (p + q) rfl U
          (ringedFiniteFreeScalarSection.{c, v, r} J φ E h (P.X p) U 1 x)
          (ringedFiniteFreeScalarSection.{c, v, r} J φ E h (Q.X q) U 1 y)))
    (hcomp : (∀ (P Q : CochainComplex (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
        (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
        (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q),
        ∃ (hEP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
          (hEQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)),
          IsIso (ε.app P) ∧ IsIso (ε.app Q) ∧
          T.map ((MR.iso J R AR P Q hP hQ).hom) ≫
              μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
              AS.tensor.map (Prod.mkHom (ε.app P) (ε.app Q)) =
            ε.app ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≫
              DerivedCategory.Q.map (κ.hom.app (P, Q)) ≫
              (MS.iso J S AS _ _ hEP hEQ).hom)) :
    ∃ (adj : E ⊣ SheafOfModules.scalarRestriction φ)
      (δ : T ⊣ SheafOfModules.scalarDerivedRestriction φ),
      (∀ (M : SheafOfModules.scalarModules J R) (V : Cᵒᵖ) (x : M.val.obj V),
        (adj.unit.app M).val.app V x = ringedFiniteFreeScalarSection.{c, v, r} J φ E h M V 1 x) ∧
      (∀ (F : CochainComplex (SheafOfModules.scalarModules J R) ℤ),
        CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) F →
        (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (F.X n)) →
        ∀ (N : CochainComplex (SheafOfModules.scalarModules J S) ℤ)
          (g : F ⟶ ((SheafOfModules.scalarRestriction φ).mapHomologicalComplex
            (.up ℤ)).obj N),
        (δ.homEquiv (DerivedCategory.Q.obj F) (DerivedCategory.Q.obj N)).symm
            (DerivedCategory.Q.map g ≫
              (SheafOfModules.scalarRestrictionComparison φ).inv.app N) =
          ε.app F ≫ DerivedCategory.Q.map
            (SheafOfModules.scalarChainTranspose.{c, v, max c v r} φ E _hE adj F N g)) ∧
    ∀ P Q : DerivedCategory (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)),
    ∃ (a : (⨁ fun _ : Fin d ↦
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P, Q)) ≅
      (SheafOfModules.scalarDerivedRestriction φ).obj
        (T.obj ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P, Q))))
      (aQ : (⨁ fun _ : Fin d ↦ Q) ≅
        (SheafOfModules.scalarDerivedRestriction φ).obj (T.obj Q))
      (β : (SheafOfModules.scalarDerivedRestriction φ).obj
        ((derivedInternalHomOfUniverses.{c, v, r, w} J S).obj (op (T.obj P), T.obj Q)) ≅
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
          (op P, (SheafOfModules.scalarDerivedRestriction φ).obj (T.obj Q))),
      RingedFiniteFreeBasisCoordinates.{c, v, r, w} J φ d e E h T ε
        ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P, Q)) a ∧
      RingedFiniteFreeBasisCoordinates.{c, v, r, w} J φ d e E h T ε Q aQ ∧
      (AR.transpose _ P ((SheafOfModules.scalarDerivedRestriction φ).obj (T.obj Q))).symm
          β.hom =
        AR.tensor.map (Prod.mkHom (𝟙 _) (δ.unit.app P)) ≫
          δ.unit.app _ ≫
          (SheafOfModules.scalarDerivedRestriction φ).map
            (μ.hom.app _ ≫ AS.tensor.map
              (Prod.mkHom (δ.counit.app _) (δ.counit.app _))) ≫
          (SheafOfModules.scalarDerivedRestriction φ).map
            (AS.evaluation (T.obj P) (T.obj Q)) ∧
      ∀ i : Fin d,
        biproduct.ι _ i ≫ a.hom ≫
          (SheafOfModules.scalarDerivedRestriction φ).map
            (AS.transpose _ (T.obj P) (T.obj Q)
              (μ.inv.app
                ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P, Q), P) ≫
                T.map (AR.evaluation P Q))) ≫ β.hom =
          (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
            (Prod.mkHom (𝟙 (op P)) (biproduct.ι _ i ≫ aQ.hom))
```

`CategoryTheory.RingedFiniteFreeBasisCoordinates` means: for every K-flat representative
F and every q : Q(F) ≅ X, the j-th basis component is the derived class of the chain map
whose n-th component on x is the scalar section e.inv(e_j)(1) tensor x. Its displayed
square includes both q and the specified universal counit. The formula determines the
chain map sectionwise, and hence determines each derived component. For d = 0 the
empty biproduct has a unique map, so no unpinned freedom remains.

The β transpose is tensor(1,eta_P), then the lax tensor map on restriction, then
restricted S-evaluation. The lax map is eta followed by U(mu and tensor(epsilon,epsilon)),
exactly as in scalarHomRestrictionTensor. The ordinary adjunction unit is 1 tensor x;
the derived adjunction is normalized on flat-term K-flat representatives by its actual
chain transpose. Thus no twisting by an arbitrary automorphism can absorb c.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeCoordinates | E8 new | stronger normalized conclusion and concrete coordinate predicate |
| Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeHom | E8 new | extracts normalized witnesses and uses their coordinate equation; signature unchanged |
| Sheaf.SixFunctors.RingedFiniteFreeHomBaseChange | E8 | consumer through Hom; original signature unchanged |

The shared tree has no copy of Coordinates or Hom yet, so downstream.py reports the
module as unknown. Searches of both the shared Lean tree and this delivery show that
Hom is the only direct consumer. All further consumers keep the same public main theorem.
The DAG citer lem-sf-ringed-finite-free-hom-transpose still holds: it uses the retained
coordinate equation; the stronger normalization clauses remove the relabelling defect.

Also fix reviewer brief point 6: tensor-data's lean.declarations contains only
CategoryTheory.ringedFiniteFreeHomBaseChange_tensor. ScalarSection remains owned by
tensor-complex, whose Data module defines it. No Lean declaration is removed.

## Status

landed 20261020T051227-L-1601075 2026-10-20 (merge of deliver/E8/Sheaf.SixFunctors.RingedFiniteFreeHomBaseChange)
