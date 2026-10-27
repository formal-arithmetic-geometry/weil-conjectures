# Completion scalar normalization predicates

## Reason

The same large existential formulas were elaborated independently in the construction statements and the point predicates. Factor their exact bodies into one generic scheme interface so type checking compares the same constants. No mathematical content, existing signature or exported name changes.

## Old

### QuotientRealization

```lean
def QuotientRealization (A : CoefficientDerivedSystemCalculus l E (point D))
    (M : CompletionUnit.OrdinaryModel l E (point D))
    (N : CompletionUnit.DerivedModel l E (point D) A M)
    (CR : quotientModel D l E) (α : CR.completion ≅ completion D l E A) : Prop :=
  (∀ K, CR.unit.app K ≫ α.hom.app K = A.adjunction.unit.app K) ∧
  ∀ (P : CochainComplex (integralTowerModules l E (point D)) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hf : ∀ i : ℤ, (P.X i).IsFlatOnSite),
    ∃ θ : (quotientTower
        (completedIntegralCommRingSheafUnrestricted l E (point D))
        (PrincipalKoszulStrictReplacement.uniformizer l E (point D))).obj P ≅
      (CompletionUnit.tower l E (point D)).obj ((M.quotient l E (point D)).obj P),
      (∀ n : ℕ,
        quotientMap (completedIntegralCommRingSheafUnrestricted l E (point D))
            (PrincipalKoszulStrictReplacement.uniformizer l E (point D)) P n ≫
            (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map θ.hom).app (op n) =
          M.augmentation l E (point D) P ≫
            limit.π ((CompletionUnit.tower l E (point D)).obj
              ((M.quotient l E (point D)).obj P)).asFunctor (op n)) ∧
      CR.counit.app P ≫ DerivedCategory.Q.map (roosF.map θ.hom) ≫
          (N.completionComparison l E (point D) P hP hf).hom =
        α.hom.app (DerivedCategory.Q.obj P)
```

### SameIndexFormula

```lean
def SameIndexFormula (F : scalarModel D l E L ι)
    (CR : quotientModel D l E) (CS : quotientModel D l L)
    (b : CR.completion ⋙ F.T ⟶ F.T ⋙ CS.completion)
    (P : CochainComplex (integralTowerModules l E (point D)) ℤ) : Prop :=
  ∃ (d : (sourceTower
          (R := completedIntegralCommRingSheafUnrestricted l E (point D))
          (PrincipalKoszulStrictReplacement.uniformizer l E (point D)) P).asFunctor ⋙
        (F.E.mapHomologicalComplex (.up ℤ) :
          CochainComplex (integralTowerModules l E (point D)) ℤ ⥤
            CochainComplex (integralTowerModules l L (point D)) ℤ) ⟶
      (targetTower
          (R := completedIntegralCommRingSheafUnrestricted l E (point D))
          (S := completedIntegralCommRingSheafUnrestricted l L (point D)) F
          (PrincipalKoszulStrictReplacement.uniformizer l L (point D)) P).asFunctor)
    (c : (F.E.mapHomologicalComplex (.up ℤ)).obj
        (roosP (sourceTower
          (R := completedIntegralCommRingSheafUnrestricted l E (point D))
          (PrincipalKoszulStrictReplacement.uniformizer l E (point D)) P)) ⟶
      roosP (targetTower
          (R := completedIntegralCommRingSheafUnrestricted l E (point D))
          (S := completedIntegralCommRingSheafUnrestricted l L (point D)) F
          (PrincipalKoszulStrictReplacement.uniformizer l L (point D)) P))
    (δ : (F.E.mapHomologicalComplex (.up ℤ)).obj
        (roosF.obj (sourceTower
          (R := completedIntegralCommRingSheafUnrestricted l E (point D))
          (PrincipalKoszulStrictReplacement.uniformizer l E (point D)) P)) ⟶
      roosF.obj (targetTower
          (R := completedIntegralCommRingSheafUnrestricted l E (point D))
          (S := completedIntegralCommRingSheafUnrestricted l L (point D)) F
          (PrincipalKoszulStrictReplacement.uniformizer l L (point D)) P)),
    (∀ n : ℕ,
      (F.E.mapHomologicalComplex (.up ℤ)).map
          (quotientMap (completedIntegralCommRingSheafUnrestricted l E (point D))
            (PrincipalKoszulStrictReplacement.uniformizer l E (point D)) P n) ≫
          d.app (op n) =
        quotientMap (completedIntegralCommRingSheafUnrestricted l L (point D))
          (PrincipalKoszulStrictReplacement.uniformizer l L (point D))
          ((F.E.mapHomologicalComplex (.up ℤ)).obj P) n) ∧
    (∀ n : ℕ, c ≫ Pi.π _ n =
      (F.E.mapHomologicalComplex (.up ℤ)).map (Pi.π _ n) ≫ d.app (op n)) ∧
    (∀ p : ℤ, δ.f (p + 1) ≫
        (roosχ (targetTower
          (R := completedIntegralCommRingSheafUnrestricted l E (point D))
          (S := completedIntegralCommRingSheafUnrestricted l L (point D)) F
          (PrincipalKoszulStrictReplacement.uniformizer l L (point D)) P) p).hom =
      scalarRoosCoordinates F.E
        (sourceTower
          (R := completedIntegralCommRingSheafUnrestricted l E (point D))
          (PrincipalKoszulStrictReplacement.uniformizer l E (point D)) P)
        (targetTower
          (R := completedIntegralCommRingSheafUnrestricted l E (point D))
          (S := completedIntegralCommRingSheafUnrestricted l L (point D)) F
          (PrincipalKoszulStrictReplacement.uniformizer l L (point D)) P) c p) ∧
    b.app (DerivedCategory.Q.obj P) ≫ CS.completion.map (F.ε.app P) ≫
        CS.counit.app ((F.E.mapHomologicalComplex (.up ℤ)).obj P) =
      F.T.map (CR.counit.app P) ≫
        F.ε.app (roosF.obj
          (sourceTower
          (R := completedIntegralCommRingSheafUnrestricted l E (point D))
          (PrincipalKoszulStrictReplacement.uniformizer l E (point D)) P)) ≫
        DerivedCategory.Q.map δ
```

### MultiplicationFormula

```lean
def MultiplicationFormula (F : scalarModel D l E L ι)
    (hE : F.E = completedOrdinaryScalarExtension l E L ι (point D))
    (CS : quotientModel D l L)
    (c : F.T ⋙ CS.completion ≅ integralScalarExtensionOfUniverses l E L ι (point D))
    (P : (integralOperationsGoodComplex l E (point D)).FullSubcategory) : Prop :=
  ∃ (μ : (targetTower
          (R := completedIntegralCommRingSheafUnrestricted l E (point D))
          (S := completedIntegralCommRingSheafUnrestricted l L (point D)) F
        (PrincipalKoszulStrictReplacement.uniformizer l L (point D)) P.obj).asFunctor ≅
      (integralScalarTowerFunctor l E L ι (point D)).obj P.obj)
    (m : roosF.obj (targetTower
          (R := completedIntegralCommRingSheafUnrestricted l E (point D))
          (S := completedIntegralCommRingSheafUnrestricted l L (point D)) F
        (PrincipalKoszulStrictReplacement.uniformizer l L (point D)) P.obj) ≅
      (integralScalarComplexFunctor l E L ι (point D)).obj P.obj),
    (∀ (i : ℤ) (n : ℕ) (U : (point D).ProEtᵒᵖ)
      (a : (completedIntegralCommRingSheafUnrestricted l L (point D)).obj.obj U)
      (x : (P.obj.X i).val.obj U),
      (((quotientMap (completedIntegralCommRingSheafUnrestricted l L (point D))
          (PrincipalKoszulStrictReplacement.uniformizer l L (point D))
          ((F.E.mapHomologicalComplex (.up ℤ)).obj P.obj) n ≫ μ.hom.app (op n)).f i).val.app U)
        ((eqToHom (congrArg (fun G : integralTowerModules l E (point D) ⥤
              integralTowerModules l L (point D) ↦ G.obj (P.obj.X i)) hE).symm :
            (completedOrdinaryScalarExtension l E L ι (point D)).obj (P.obj.X i) ⟶
              F.E.obj (P.obj.X i)).val.app U
          (completedScalarTensorSection l E L ι (point D) (P.obj.X i) U a x)) =
        integralScalarTensorSection l E L ι (point D) n (P.obj.X i) U
          ((completedIntegralCommRingProjectionUnrestricted l L (point D) n).hom.app U a) x) ∧
    (∀ p : ℤ, m.hom.f (p + 1) ≫
        biprod.lift
          ((CochainComplex.mappingCocone.snd
            (completedScalarRoosEndomorphism l E L ι (point D) P.obj)).v
              (p + 1) p (by omega))
          ((CochainComplex.mappingCocone.fst
            (completedScalarRoosEndomorphism l E L ι (point D) P.obj)).f (p + 1)) =
      (roosχ (targetTower
          (R := completedIntegralCommRingSheafUnrestricted l E (point D))
          (S := completedIntegralCommRingSheafUnrestricted l L (point D)) F
        (PrincipalKoszulStrictReplacement.uniformizer l L (point D)) P.obj) p).hom ≫
        biprod.map ((Limits.Pi.map (fun n : ℕ ↦ μ.hom.app (op n))).f p)
          ((Limits.Pi.map (fun n : ℕ ↦ μ.hom.app (op n))).f (p + 1))) ∧
    CS.completion.map (F.ε.app P.obj) ≫
        CS.counit.app ((F.E.mapHomologicalComplex (.up ℤ)).obj P.obj) ≫
          DerivedCategory.Q.map m.hom =
      c.hom.app (DerivedCategory.Q.obj P.obj) ≫
        (integralScalarExtensionComparisonOfUniverses l E L ι (point D)).hom.app P
```

## New

```lean
def QuotientRealization (A : CoefficientDerivedSystemCalculus l E (point D))
    (M : CompletionUnit.OrdinaryModel l E (point D))
    (N : CompletionUnit.DerivedModel l E (point D) A M)
    (CR : quotientModel D l E) (α : CR.completion ≅ completion D l E A) : Prop :=
  ModelData.QuotientRealization l E (point D) A M N CR α
```

```lean
def SameIndexFormula (F : scalarModel D l E L ι)
    (CR : quotientModel D l E) (CS : quotientModel D l L)
    (b : CR.completion ⋙ F.T ⟶ F.T ⋙ CS.completion)
    (P : CochainComplex (integralTowerModules l E (point D)) ℤ) : Prop :=
  ModelData.SameIndexFormula l E L ι (point D) F CR CS b P
```

```lean
def MultiplicationFormula (F : scalarModel D l E L ι)
    (hE : F.E = completedOrdinaryScalarExtension l E L ι (point D))
    (CS : quotientModel D l L)
    (c : F.T ⋙ CS.completion ≅ integralScalarExtensionOfUniverses l E L ι (point D))
    (P : (integralOperationsGoodComplex l E (point D)).FullSubcategory) : Prop :=
  ModelData.MultiplicationFormula l E L ι (point D) F hE CS c P
```

The new ModelData predicates have exactly the old right hand sides, with `(point D)` replaced by `W`. Their model abbreviations retain the same universe and canonical-instance arguments.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PodCompletionUnitScalarIntertwining | V9 | Same definitions by definitional equality; proof uses shared formulas. |
| Sheaf.Paper.PodReconstructionCommonStageCoherence | unclaimed in the local claim records | The exported theorem type and predicates remain definitionally equal. |
| Sheaf.Paper.PodReconstructionRawRationalNaturality | unclaimed in the local claim records | The exported theorem type and predicates remain definitionally equal. |

The name search finds QuotientRealization and SameIndexFormula in the assigned module and PodReconstructionCommonStageCoherence, and MultiplicationFormula only in the assigned module. The two downstream modules listed are the full module import closure. Their uses are signatures, and the predicates remain definitionally equal. No consumer adaptation is required. No Challenge statement or definition meaning changes.

## Status

landed 20261025T205945-L-3425099 2026-10-25 (merge of deliver/V9/Sheaf.Paper.PodCompletionUnitScalarIntertwining)
