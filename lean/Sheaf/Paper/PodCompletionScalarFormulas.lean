/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V9
-/
module

public import Sheaf.Paper.CompletionUnitModels
public import Sheaf.Algebra.Homology.FiniteFreeCompletionExchange
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.Paper.PrincipalKoszulStrictReplacement

/-! # Shared completion scalar normalization formulas -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall

attribute [local irreducible] HasDerivedCategory.standard
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local irreducible] CategoryTheory.PrincipalQuotientCompletion.quotientTower
  CategoryTheory.roosF SheafOfModules.monoidalCategory

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.PrincipalQuotientCompletion
namespace WeilConjectures.PodCompletionScalar.ModelData

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

/-- Canonical normalization formula, shared by the construction and its assembly.
Source: Bhatt--Scholze Definitions 3.5.2--3.5.3 and Lemma 6.8.2(1)
(blueprint: def-pod-completion-scalar-formulas). -/
abbrev quotientModel :=
  @Model.{t + 1, t, max u (t + 1), max u (t + 1) + 1}
    W.ProEt inferInstance (essentiallySmallSelf.{u} _)
    (Scheme.ProEt.topology W) inferInstance
    (integralCoefficientAbSheafify.{t, u} W)
    (integralCoefficientAbLocallyBijective.{t, u} W)
    (completedIntegralCommRingSheafUnrestricted l E W)
    (integralTowerHasDerivedCategory l E W)
    (PrincipalKoszulStrictReplacement.uniformizer l E W)

/-- Canonical normalization formula, shared by the construction and its assembly.
Source: Bhatt--Scholze Definitions 3.5.2--3.5.3 and Lemma 6.8.2(1)
(blueprint: def-pod-completion-scalar-formulas). -/
abbrev scalarModel :=
  @SheafOfModules.DerivedChangeOfRingsCochainModel.{t + 1, t, max u (t + 1),
    max u (t + 1) + 1, max u (t + 1) + 1}
    W.ProEt inferInstance (essentiallySmallSelf.{u} _)
    (Scheme.ProEt.topology W) inferInstance
    (integralCoefficientAbLocallyBijective.{t, u} W)
    (integralCoefficientAbSheafify.{t, u} W)
    (completedIntegralCommRingSheafUnrestricted l E W)
    (completedIntegralCommRingSheafUnrestricted l L W)
    (completedCoefficientMap l E L ι W)
    (integralTowerHasDerivedCategory l E W)
    (integralTowerHasDerivedCategory l L W)

/-- Canonical normalization formula, shared by the construction and its assembly.
Source: Bhatt--Scholze Definitions 3.5.2--3.5.3 and Lemma 6.8.2(1)
(blueprint: def-pod-completion-scalar-formulas). -/
def QuotientRealization (A : CoefficientDerivedSystemCalculus l E W)
    (M : CompletionUnit.OrdinaryModel l E W)
    (N : CompletionUnit.DerivedModel l E W A M)
    (CR : quotientModel l E W)
    (α : CR.completion ≅ A.reduction ⋙ coefficientSequenceLimit l E W) : Prop :=
  (∀ K, CR.unit.app K ≫ α.hom.app K = A.adjunction.unit.app K) ∧
  ∀ (P : CochainComplex (integralTowerModules l E W) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hf : ∀ i : ℤ, (P.X i).IsFlatOnSite),
    ∃ θ : (quotientTower
        (completedIntegralCommRingSheafUnrestricted l E W)
        (PrincipalKoszulStrictReplacement.uniformizer l E W)).obj P ≅
      (CompletionUnit.tower l E W).obj ((M.quotient l E W).obj P),
      (∀ n : ℕ,
        quotientMap (completedIntegralCommRingSheafUnrestricted l E W)
            (PrincipalKoszulStrictReplacement.uniformizer l E W) P n ≫
            (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map θ.hom).app (op n) =
          M.augmentation l E W P ≫
            limit.π ((CompletionUnit.tower l E W).obj
              ((M.quotient l E W).obj P)).asFunctor (op n)) ∧
      CR.counit.app P ≫ DerivedCategory.Q.map (roosF.map θ.hom) ≫
          (N.completionComparison l E W P hP hf).hom =
        α.hom.app (DerivedCategory.Q.obj P)

/-- Canonical normalization formula, shared by the construction and its assembly.
Source: Bhatt--Scholze Definitions 3.5.2--3.5.3 and Lemma 6.8.2(1)
(blueprint: def-pod-completion-scalar-formulas). -/
def SameIndexFormula (F : scalarModel l E L ι W)
    (CR : quotientModel l E W) (CS : quotientModel l L W)
    (b : CR.completion ⋙ F.T ⟶ F.T ⋙ CS.completion)
    (P : CochainComplex (integralTowerModules l E W) ℤ) : Prop :=
  ∃ (d : (sourceTower
          (R := completedIntegralCommRingSheafUnrestricted l E W)
          (PrincipalKoszulStrictReplacement.uniformizer l E W) P).asFunctor ⋙
        (F.E.mapHomologicalComplex (.up ℤ) :
          CochainComplex (integralTowerModules l E W) ℤ ⥤
            CochainComplex (integralTowerModules l L W) ℤ) ⟶
      (targetTower
          (R := completedIntegralCommRingSheafUnrestricted l E W)
          (S := completedIntegralCommRingSheafUnrestricted l L W) F
          (PrincipalKoszulStrictReplacement.uniformizer l L W) P).asFunctor)
    (c : (F.E.mapHomologicalComplex (.up ℤ)).obj
        (roosP (sourceTower
          (R := completedIntegralCommRingSheafUnrestricted l E W)
          (PrincipalKoszulStrictReplacement.uniformizer l E W) P)) ⟶
      roosP (targetTower
          (R := completedIntegralCommRingSheafUnrestricted l E W)
          (S := completedIntegralCommRingSheafUnrestricted l L W) F
          (PrincipalKoszulStrictReplacement.uniformizer l L W) P))
    (δ : (F.E.mapHomologicalComplex (.up ℤ)).obj
        (roosF.obj (sourceTower
          (R := completedIntegralCommRingSheafUnrestricted l E W)
          (PrincipalKoszulStrictReplacement.uniformizer l E W) P)) ⟶
      roosF.obj (targetTower
          (R := completedIntegralCommRingSheafUnrestricted l E W)
          (S := completedIntegralCommRingSheafUnrestricted l L W) F
          (PrincipalKoszulStrictReplacement.uniformizer l L W) P)),
    (∀ n : ℕ,
      (F.E.mapHomologicalComplex (.up ℤ)).map
          (quotientMap (completedIntegralCommRingSheafUnrestricted l E W)
            (PrincipalKoszulStrictReplacement.uniformizer l E W) P n) ≫
          d.app (op n) =
        quotientMap (completedIntegralCommRingSheafUnrestricted l L W)
          (PrincipalKoszulStrictReplacement.uniformizer l L W)
          ((F.E.mapHomologicalComplex (.up ℤ)).obj P) n) ∧
    (∀ n : ℕ, c ≫ Pi.π _ n =
      (F.E.mapHomologicalComplex (.up ℤ)).map (Pi.π _ n) ≫ d.app (op n)) ∧
    (∀ p : ℤ, δ.f (p + 1) ≫
        (roosχ (targetTower
          (R := completedIntegralCommRingSheafUnrestricted l E W)
          (S := completedIntegralCommRingSheafUnrestricted l L W) F
          (PrincipalKoszulStrictReplacement.uniformizer l L W) P) p).hom =
      scalarRoosCoordinates F.E
        (sourceTower
          (R := completedIntegralCommRingSheafUnrestricted l E W)
          (PrincipalKoszulStrictReplacement.uniformizer l E W) P)
        (targetTower
          (R := completedIntegralCommRingSheafUnrestricted l E W)
          (S := completedIntegralCommRingSheafUnrestricted l L W) F
          (PrincipalKoszulStrictReplacement.uniformizer l L W) P) c p) ∧
    b.app (DerivedCategory.Q.obj P) ≫ CS.completion.map (F.ε.app P) ≫
        CS.counit.app ((F.E.mapHomologicalComplex (.up ℤ)).obj P) =
      F.T.map (CR.counit.app P) ≫
        F.ε.app (roosF.obj
          (sourceTower
          (R := completedIntegralCommRingSheafUnrestricted l E W)
          (PrincipalKoszulStrictReplacement.uniformizer l E W) P)) ≫
        DerivedCategory.Q.map δ

/-- Canonical normalization formula, shared by the construction and its assembly.
Source: Bhatt--Scholze Definitions 3.5.2--3.5.3 and Lemma 6.8.2(1)
(blueprint: def-pod-completion-scalar-formulas). -/
def MultiplicationFormula (F : scalarModel l E L ι W)
    (hE : F.E = completedOrdinaryScalarExtension l E L ι W)
    (CS : quotientModel l L W)
    (c : F.T ⋙ CS.completion ≅ integralScalarExtensionOfUniverses l E L ι W)
    (P : (integralOperationsGoodComplex l E W).FullSubcategory) : Prop :=
  ∃ (μ : (targetTower
          (R := completedIntegralCommRingSheafUnrestricted l E W)
          (S := completedIntegralCommRingSheafUnrestricted l L W) F
        (PrincipalKoszulStrictReplacement.uniformizer l L W) P.obj).asFunctor ≅
      (integralScalarTowerFunctor l E L ι W).obj P.obj)
    (m : roosF.obj (targetTower
          (R := completedIntegralCommRingSheafUnrestricted l E W)
          (S := completedIntegralCommRingSheafUnrestricted l L W) F
        (PrincipalKoszulStrictReplacement.uniformizer l L W) P.obj) ≅
      (integralScalarComplexFunctor l E L ι W).obj P.obj),
    (∀ (i : ℤ) (n : ℕ) (U : W.ProEtᵒᵖ)
      (a : (completedIntegralCommRingSheafUnrestricted l L W).obj.obj U)
      (x : (P.obj.X i).val.obj U),
      (((quotientMap (completedIntegralCommRingSheafUnrestricted l L W)
          (PrincipalKoszulStrictReplacement.uniformizer l L W)
          ((F.E.mapHomologicalComplex (.up ℤ)).obj P.obj) n ≫ μ.hom.app (op n)).f i).val.app U)
        ((eqToHom (congrArg (fun G : integralTowerModules l E W ⥤
              integralTowerModules l L W ↦ G.obj (P.obj.X i)) hE).symm :
            (completedOrdinaryScalarExtension l E L ι W).obj (P.obj.X i) ⟶
              F.E.obj (P.obj.X i)).val.app U
          (completedScalarTensorSection l E L ι W (P.obj.X i) U a x)) =
        integralScalarTensorSection l E L ι W n (P.obj.X i) U
          ((completedIntegralCommRingProjectionUnrestricted l L W n).hom.app U a) x) ∧
    (∀ p : ℤ, m.hom.f (p + 1) ≫
        biprod.lift
          ((CochainComplex.mappingCocone.snd
            (completedScalarRoosEndomorphism l E L ι W P.obj)).v
              (p + 1) p (by omega))
          ((CochainComplex.mappingCocone.fst
            (completedScalarRoosEndomorphism l E L ι W P.obj)).f (p + 1)) =
      (roosχ (targetTower
          (R := completedIntegralCommRingSheafUnrestricted l E W)
          (S := completedIntegralCommRingSheafUnrestricted l L W) F
        (PrincipalKoszulStrictReplacement.uniformizer l L W) P.obj) p).hom ≫
        biprod.map ((Limits.Pi.map (fun n : ℕ ↦ μ.hom.app (op n))).f p)
          ((Limits.Pi.map (fun n : ℕ ↦ μ.hom.app (op n))).f (p + 1))) ∧
    CS.completion.map (F.ε.app P.obj) ≫
        CS.counit.app ((F.E.mapHomologicalComplex (.up ℤ)).obj P.obj) ≫
          DerivedCategory.Q.map m.hom =
      c.hom.app (DerivedCategory.Q.obj P.obj) ≫
        (integralScalarExtensionComparisonOfUniverses l E L ι W).hom.app P

end WeilConjectures.PodCompletionScalar.ModelData
