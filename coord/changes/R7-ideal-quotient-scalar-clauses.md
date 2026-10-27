# CategoryTheory.RingedSiteIdeal.ideal_quotient_tower_scalar_associator

## Reason

The raw ten-clause conjunction repeatedly unfolds the large concrete sheaf tensor
functors during proof checking and exceeds the single-file compile limit. Name the
clauses by transparent predicates and prove the coherence calculations for generic
functor families before specializing them. The eight existential witnesses and all
ten original conclusions are retained. Expanding the predicate definitions gives
the original statement by definitional equality (including proof irrelevance for
zero-preservation instances). This is an interface factoring, not a weakening.
All proof code stays in the original module. No target signature, existing public
helper definition, public import, or adopted source-library declaration changes.

## Old

```lean
theorem ideal_quotient_tower_scalar_associator :
    ∃ (q : ∀ (R : Sheaf J CommRingCat.{u}) (I' I : RingedSiteIdeal R),
        IsContained I' I → (quotientCoefficient I' ⟶ quotientCoefficient I))
      (hmono : ∀ (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S)
        (I' I : RingedSiteIdeal R), IsContained I' I →
          IsContained (I'.extension a) (I.extension a))
      (hcomp : ∀ (R S V : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (b : S ⟶ V)
        (I : RingedSiteIdeal R), (I.extension a).extension b = I.extension (a ≫ b))
      (hid : ∀ (R : Sheaf J CommRingCat.{u}) (I : RingedSiteIdeal R),
        I.extension (𝟙 R) = I)
      (uMap : ∀ (R : Sheaf J CommRingCat.{u}) (I : RingedSiteIdeal R),
        𝟭 (SheafOfModules.{u} (siteModuleRings R)) ⟶ idealTensorFunctor I)
      (α : ∀ (R S V : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (b : S ⟶ V),
        SheafOfModules.RingedTensor.tensorFunctor a ⋙
          SheafOfModules.RingedTensor.tensorFunctor b ≅
            SheafOfModules.RingedTensor.tensorFunctor (a ≫ b))
      (ε : ∀ R : Sheaf J CommRingCat.{u},
        SheafOfModules.RingedTensor.tensorFunctor (𝟙 R) ≅
          𝟭 (SheafOfModules.{u} (siteModuleRings R)))
      (β : ∀ (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (I : RingedSiteIdeal R),
        idealTensorFunctor I ⋙ SheafOfModules.RingedTensor.tensorFunctor a ≅
          SheafOfModules.RingedTensor.tensorFunctor a ⋙ idealTensorFunctor (I.extension a)),
    (∀ (R : Sheaf J CommRingCat.{u}) (I' I : RingedSiteIdeal R) (h : IsContained I' I)
      (W : Cᵒᵖ) (s : (ringQuotient I').obj.obj W),
      (q R I' I h).val.app W s = (ringTransition h).hom.app W s) ∧
    (∀ (R : Sheaf J CommRingCat.{u}) (I : RingedSiteIdeal R)
      (M : SheafOfModules.{u} (siteModuleRings R)) (W : Cᵒᵖ) (p : M.val.obj W),
      ((uMap R I).app M).val.app W p =
        SheafOfModules.RingedTensor.pure R M (quotientCoefficient I) W p
          (1 : (ringQuotient I).obj.obj W)) ∧
    (∀ (R S V : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (b : S ⟶ V)
      (M : SheafOfModules.{u} (siteModuleRings R)) (W : Cᵒᵖ)
      (p : M.val.obj W) (s : S.obj.obj W) (v : V.obj.obj W),
      ((α R S V a b).hom.app M).val.app W
        (idealScalarPure b _ W (idealScalarPure a M W p s) v) =
          idealScalarPure (a ≫ b) M W p (b.hom.app W s * v)) ∧
    (∀ (R : Sheaf J CommRingCat.{u}) (M : SheafOfModules.{u} (siteModuleRings R))
      (W : Cᵒᵖ) (p : M.val.obj W) (r : R.obj.obj W),
      ((ε R).hom.app M).val.app W (idealScalarPure (𝟙 R) M W p r) = r • p) ∧
    (∀ (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (I : RingedSiteIdeal R)
      (M : SheafOfModules.{u} (siteModuleRings R)) (W : Cᵒᵖ)
      (p : M.val.obj W) (r : R.obj.obj W) (s : S.obj.obj W),
      ((β R S a I).hom.app M).val.app W
        (idealScalarPure a _ W
          (SheafOfModules.RingedTensor.pure R M (quotientCoefficient I) W p
            ((ringProjection I).hom.app W r)) s) =
      SheafOfModules.RingedTensor.pure S _ (quotientCoefficient (I.extension a)) W
        (idealScalarPure a M W p s)
        ((ringProjection (I.extension a)).hom.app W (a.hom.app W r))) ∧
    (∀ (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (I : RingedSiteIdeal R)
      (M : SheafOfModules.{u} (siteModuleRings R)),
      (SheafOfModules.RingedTensor.tensorFunctor a).map ((uMap R I).app M) ≫
        (β R S a I).hom.app M =
      (uMap S (I.extension a)).app ((SheafOfModules.RingedTensor.tensorFunctor a).obj M)) ∧
    (∀ (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (I' I : RingedSiteIdeal R)
      (h : IsContained I' I) (M : SheafOfModules.{u} (siteModuleRings R)),
      (SheafOfModules.RingedTensor.tensorFunctor a).map
          (((curriedTensor _).flip.map (q R I' I h)).app M) ≫
        (β R S a I).hom.app M =
      (β R S a I').hom.app M ≫
        (((curriedTensor _).flip.map
          (q S (I'.extension a) (I.extension a) (hmono R S a I' I h))).app
            ((SheafOfModules.RingedTensor.tensorFunctor a).obj M))) ∧
    (∀ (R S V : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (b : S ⟶ V)
      (I : RingedSiteIdeal R) (M : SheafOfModules.{u} (siteModuleRings R)),
      (SheafOfModules.RingedTensor.tensorFunctor b).map ((β R S a I).hom.app M) ≫
        (β S V b (I.extension a)).hom.app
          ((SheafOfModules.RingedTensor.tensorFunctor a).obj M) ≫
        eqToHom (congrArg (fun L ↦ (idealTensorFunctor L).obj
          ((SheafOfModules.RingedTensor.tensorFunctor b).obj
            ((SheafOfModules.RingedTensor.tensorFunctor a).obj M))) (hcomp R S V a b I)) ≫
        (idealTensorFunctor (I.extension (a ≫ b))).map ((α R S V a b).hom.app M) =
      (α R S V a b).hom.app ((idealTensorFunctor I).obj M) ≫
        (β R V (a ≫ b) I).hom.app M) ∧
    (∀ (R : Sheaf J CommRingCat.{u}) (I : RingedSiteIdeal R)
      (M : SheafOfModules.{u} (siteModuleRings R)),
      (β R R (𝟙 R) I).hom.app M ≫
        (idealTensorFunctor (I.extension (𝟙 R))).map ((ε R).hom.app M) ≫
        eqToHom (congrArg (fun L ↦ (idealTensorFunctor L).obj M) (hid R I)) =
      (ε R).hom.app ((idealTensorFunctor I).obj M)) ∧
    (∀ (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S)
      (I : ℕ → RingedSiteIdeal R) (hI : ∀ n, IsContained (I (n + 1)) (I n)),
      ∃ B : ∀ P : CochainComplex (SheafOfModules.{u} (siteModuleRings R)) ℤ,
        idealComplexTower I (fun n ↦ q R _ _ (hI n)) P ⋙
            (SheafOfModules.RingedTensor.tensorFunctor a).mapHomologicalComplex (.up ℤ) ≅
          idealComplexTower (fun n ↦ (I n).extension a)
            (fun n ↦ q S _ _ (hmono R S a _ _ (hI n)))
            (((SheafOfModules.RingedTensor.tensorFunctor a).mapHomologicalComplex
              (.up ℤ)).obj P),
      (∀ (P : CochainComplex (SheafOfModules.{u} (siteModuleRings R)) ℤ) (n : ℕ) (k : ℤ),
        ((B P).hom.app (op n)).f k = (β R S a (I n)).hom.app (P.X k)) ∧
      (∀ (P P' : CochainComplex (SheafOfModules.{u} (siteModuleRings R)) ℤ)
        (f : P ⟶ P') (n : ℕ),
        ((SheafOfModules.RingedTensor.tensorFunctor a).mapHomologicalComplex (.up ℤ)).map
          (((idealTensorFunctor (I n)).mapHomologicalComplex (.up ℤ)).map f) ≫
            (B P').hom.app (op n) =
          (B P).hom.app (op n) ≫
            ((idealTensorFunctor ((I n).extension a)).mapHomologicalComplex (.up ℤ)).map
              (((SheafOfModules.RingedTensor.tensorFunctor a).mapHomologicalComplex
                (.up ℤ)).map f)))
```

## New

```lean
theorem ideal_quotient_tower_scalar_associator :
    ∃ (q : ∀ (R : Sheaf J CommRingCat.{u}) (I' I : RingedSiteIdeal R),
        IsContained I' I → (quotientCoefficient I' ⟶ quotientCoefficient I))
      (hmono : ∀ (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S)
        (I' I : RingedSiteIdeal R), IsContained I' I →
          IsContained (I'.extension a) (I.extension a))
      (hcomp : ∀ (R S V : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (b : S ⟶ V)
        (I : RingedSiteIdeal R), (I.extension a).extension b = I.extension (a ≫ b))
      (hid : ∀ (R : Sheaf J CommRingCat.{u}) (I : RingedSiteIdeal R),
        I.extension (𝟙 R) = I)
      (uMap : ∀ (R : Sheaf J CommRingCat.{u}) (I : RingedSiteIdeal R),
        𝟭 (SheafOfModules.{u} (siteModuleRings R)) ⟶ idealTensorFunctor I)
      (α : ∀ (R S V : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (b : S ⟶ V),
        SheafOfModules.RingedTensor.tensorFunctor a ⋙
          SheafOfModules.RingedTensor.tensorFunctor b ≅
            SheafOfModules.RingedTensor.tensorFunctor (a ≫ b))
      (ε : ∀ R : Sheaf J CommRingCat.{u},
        SheafOfModules.RingedTensor.tensorFunctor (𝟙 R) ≅
          𝟭 (SheafOfModules.{u} (siteModuleRings R)))
      (β : ∀ (R S : Sheaf J CommRingCat.{u}) (a : R ⟶ S) (I : RingedSiteIdeal R),
        idealTensorFunctor I ⋙ SheafOfModules.RingedTensor.tensorFunctor a ≅
          SheafOfModules.RingedTensor.tensorFunctor a ⋙ idealTensorFunctor (I.extension a)),
    IdealScalarTransitionFormula q ∧
    IdealScalarUnitFormula uMap ∧
    IdealScalarAssociatorFormula α ∧
    IdealScalarIdentityFormula ε ∧
    IdealScalarQuotientFormula β ∧
    IdealScalarAugmentationCompatibility uMap β ∧
    IdealScalarTransitionCompatibility q hmono β ∧
    IdealScalarCompositionCompatibility hcomp α β ∧
    IdealScalarIdentityCompatibility hid ε β ∧
    IdealScalarTowerCompatibility q hmono β
```

The ten `IdealScalar...` predicates are transparent definitions of the original
clauses. Clauses 6--10 specialize the transparent `ScalarQuotient...Law` predicates
to the existing scalar and quotient tensor functors. `scalarQuotientComplexTower`
and `scalarQuotientComplexTransition` specialize definitionally to the existing
`idealComplexTower` and `idealComplexTransition`. The public proofs
`scalarZeroFamily` and `quotientZeroFamily` supply the existing zero-preservation
instances used in the complex predicates; they introduce no assumption.

## Users

`tools/downstream.py Sheaf.Paper.IdealQuotientTowerScalarAssociator --uses
ideal_quotient_tower_scalar_associator` reports zero downstream modules and one
textual user (the item's own declaration).

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IdealQuotientTowerScalarAssociator | R7 | Complete proof; definitionally equal named conclusion clauses. |

The DAG parents `lem-a1-balanced-finite-tower-generator-comparison`,
`lem-sp-field-scalar-normalized-systems`,
`lem-pur-compact-support-strict-scalar-composition`, and
`lem-pur-finite-free-completion-exchange-coherence` still need this result. Their
mathematical statements and dependencies are unchanged; the original equations
remain available by unfolding the named predicates. No parent is withdrawn and no
consumer adaptation is required. No definition used in a Challenge target changes.

## Status

landed 20261024T190851-L-124858 2026-10-24 (merge of deliver/R7/Sheaf.Paper.IdealQuotientTowerScalarAssociator)
