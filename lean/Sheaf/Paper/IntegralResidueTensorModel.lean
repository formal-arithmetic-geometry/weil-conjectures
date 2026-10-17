/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralResidueTensorPresentation
public import Sheaf.Paper.IntegralResidueOrdinaryMonoidal
public import Sheaf.Paper.IntegralResidueDerivedMonoidal

/-! # A common homotopy-level model for the residue tensor square

Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15.
(blueprint: new-integral-residue-tensor-model)
-/

@[expose] public section

noncomputable section

universe v u u₁ u₂
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v + 1} C] [Abelian C] [IsGrothendieckAbelian.{v + 1} C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{v + 1} D] [Abelian D] [IsGrothendieckAbelian.{v + 1} D]
  [MonoidalCategory D] [MonoidalClosed D] [MonoidalPreadditive D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

local instance : BraidedCategory (DerivedCategory D) :=
  DerivedMonoidal.braidedCategory (DerivedCategory.Qh (C := D))
    (HomotopyCategory.quasiIso D (.up ℤ))

/-- The fixed coefficient concentrated in degree zero in the homotopy category.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; explicit tensor comparisons.
(blueprint: new-integral-residue-tensor-model) -/
noncomputable abbrev tensorModelCoefficient (B : C) :=
  (HomotopyCategory.quotient C (.up ℤ)).obj
    ((HomologicalComplex.single C (.up ℤ) 0).obj B)

/-- The standard comparison between the two degree-zero presentations.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; explicit tensor comparisons.
(blueprint: new-integral-residue-tensor-model) -/
noncomputable def tensorModelCoefficientIso (B : C) :
    (DerivedCategory.singleFunctor C 0).obj B ≅
      DerivedCategory.Qh.obj (tensorModelCoefficient B) :=
  (DerivedCategory.singleFunctorIsoCompQ C 0).app B ≪≫
    (DerivedCategory.quotientCompQhIso C).symm.app _

/-- Compare the derived target with the ordinary tensor after applying F.
The final tensor factor is K-flat on the representatives used below.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; explicit tensor comparisons.
(blueprint: new-integral-residue-tensor-model) -/
@[irreducible] noncomputable def tensorModelTarget (B : C) (P : HomotopyCategory C (.up ℤ)) :
    F.leftDerivedFunctor.obj (DerivedCategory.Qh.obj P) ⊗
        F.leftDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj B) ⟶
      DerivedCategory.Qh.obj
        ((F.mapHomotopyCategory (.up ℤ)).obj (tensorModelCoefficient B) ⊗
          (F.mapHomotopyCategory (.up ℤ)).obj P) :=
  (β_ (F.leftDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj B))
    (F.leftDerivedFunctor.obj (DerivedCategory.Qh.obj P))).inv ≫
    ((F.leftDerivedFunctor.map (tensorModelCoefficientIso B).hom ≫
      F.leftDerivedFunctorCounit.app (tensorModelCoefficient B)) ⊗ₘ
      F.leftDerivedFunctorCounit.app P) ≫
    LaxMonoidal.μ (DerivedCategory.Qh (C := D))
      ((F.mapHomotopyCategory (.up ℤ)).obj (tensorModelCoefficient B))
      ((F.mapHomotopyCategory (.up ℤ)).obj P)

/-- The target comparison is invertible on representatives with K-flat image.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; explicit tensor comparisons.
(blueprint: new-integral-residue-tensor-model) -/
theorem tensorModelTarget_isIso (B : C) (P : HomotopyCategory C (.up ℤ))
    (hP : F.kFlatMap P) : IsIso (tensorModelTarget F B P) := by
  have := isIso_μNatTrans_Qh_app_app_of_kFlat
    ((F.mapHomotopyCategory (.up ℤ)).obj (tensorModelCoefficient B)) _ hP
  have : IsIso (F.leftDerivedFunctorCounit.app (tensorModelCoefficient B)) :=
    inferInstance
  have : IsIso (F.leftDerivedFunctorCounit.app P) := inferInstance
  have : IsIso (LaxMonoidal.μ (DerivedCategory.Qh (C := D))
      ((F.mapHomotopyCategory (.up ℤ)).obj (tensorModelCoefficient B))
      ((F.mapHomotopyCategory (.up ℤ)).obj P)) := ‹_›
  unfold tensorModelTarget
  infer_instance

variable [F.IsLeftAdjoint] [F.Monoidal]

/-- The common map: the tensor counit, the exact-F counit, then the ordinary
comonoidal comparison.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; explicit tensor comparisons.
(blueprint: new-integral-residue-tensor-model) -/
noncomputable def tensorModelMap (B : C) (H : DerivedCategory C ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ H ⟶
      (tensorLeft B).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : HomotopyCategory C (.up ℤ)) :
    F.leftDerivedFunctor.obj (H.obj (DerivedCategory.Qh.obj P)) ⟶
      DerivedCategory.Qh.obj
        ((F.mapHomotopyCategory (.up ℤ)).obj (tensorModelCoefficient B) ⊗
          (F.mapHomotopyCategory (.up ℤ)).obj P) :=
  F.leftDerivedFunctor.map (ε.app P) ≫ F.leftDerivedFunctorCounit.app _ ≫
    DerivedCategory.Qh.map
      ((F.mapHomotopyCategory (.up ℤ)).map
          ((CategoryTheory.homotopyTensorSingleIso B).inv.app P) ≫
        ((OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app
          (tensorModelCoefficient B)).app P)

end CategoryTheory.Functor

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- The residue coefficient as an ordinary integral module.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; explicit tensor comparisons.
(blueprint: new-integral-residue-tensor-model) -/
noncomputable abbrev residueExchangeOrdinaryCoefficient (T : Scheme.{u}) :=
  (Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).obj
    (Mod.regular (condensedRingObj
      (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) T))

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

variable (P : HomotopyCategory
  (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (condensedRingObj (integralCoeff ℓ E) Y)) (.up ℤ))

/-- The explicit comparison from the target of the residue square to its ordinary model.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; explicit tensor comparisons.
(blueprint: new-integral-residue-tensor-model) -/
@[irreducible]
noncomputable def residueExchangeTensorModelTarget :
    (residueExchangeUpperStar (integralCoeff ℓ E) f).obj (DerivedCategory.Qh.obj P) ⊗
        (residueExchangeUpperStar (integralCoeff ℓ E) f).obj
          (residueExchangeCoefficient ℓ E Y) ⟶
      DerivedCategory.Qh.obj
        (((f)^*⟦integralCoeff ℓ E⟧.mapHomotopyCategory (.up ℤ)).obj
            (Functor.tensorModelCoefficient (residueExchangeOrdinaryCoefficient ℓ E Y)) ⊗
          ((f)^*⟦integralCoeff ℓ E⟧.mapHomotopyCategory (.up ℤ)).obj P) := by
  unfold residueExchangeUpperStar
  exact Functor.tensorModelTarget (f)^*⟦integralCoeff ℓ E⟧
    (residueExchangeOrdinaryCoefficient ℓ E Y) P

/-- The explicit common map for the two routes in the residue square.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; explicit tensor comparisons.
(blueprint: new-integral-residue-tensor-model) -/
noncomputable def residueExchangeTensorModelMap :
    (residueExchangeUpperStar (integralCoeff ℓ E) f).obj
        ((residueExchangeRestriction ℓ E Y).obj
          ((residueExchangeReduction ℓ E Y).obj (DerivedCategory.Qh.obj P))) ⟶
      DerivedCategory.Qh.obj
        (((f)^*⟦integralCoeff ℓ E⟧.mapHomotopyCategory (.up ℤ)).obj
            (Functor.tensorModelCoefficient (residueExchangeOrdinaryCoefficient ℓ E Y)) ⊗
          ((f)^*⟦integralCoeff ℓ E⟧.mapHomotopyCategory (.up ℤ)).obj P) := by
  let := residueExchangeOrdinaryPullMonoidal ℓ E f
  unfold residueExchangeUpperStar
  exact Functor.tensorModelMap (f)^*⟦integralCoeff ℓ E⟧
    (residueExchangeOrdinaryCoefficient ℓ E Y)
    (residueExchangeReduction ℓ E Y ⋙ residueExchangeRestriction ℓ E Y)
    (by
      unfold residueExchangeReduction integralReduction residueExchangeRestriction
      exact Mod.tensorPresentationDerivedCounit (coefficientMap (integralReductionMap ℓ E) Y)) P

end AlgebraicGeometry.ProEtale.CondensedRing
