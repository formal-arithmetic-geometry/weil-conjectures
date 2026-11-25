/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueTensorPullPresentation
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueScalarCounitModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueTensorPullCounitCore

/-! Normalization of the coefficient-adjusted tensor presentation on X.

## References

- Bhatt--Scholze, *The pro-étale topology for schemes*, Remark 6.8.15.
-/

@[expose] public section

universe u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance instEssentiallySmallProfinite_integralResidueTensorPullCounitModel
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
/-- The tensor-pull presentation followed by its ordinary model comparison is
its defining tensor-presentation counit, with the ordinary coefficient identified.
Only the X presentation occurs; there is no scalar pull mate in this identity. -/
theorem integralResidue_tensorPullCounit_model {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)) (.up ℤ)) :
    let F := (f)^*⟦integralCoeff ℓ E⟧
    let B := residueExchangeOrdinaryCoefficient ℓ E Y
    let B' := residueExchangeOrdinaryCoefficient ℓ E X
    let A := Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)
    let SX := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (coefficientMap (integralReductionMap ℓ E) X)
    letI := residueOrdinaryUpperStarMonoidal A f
    let e : F.obj B ≅ B' :=
      residueOrdinaryRestrictedRegularPullIso (integralCoeff ℓ E) A
        (integralReductionMap ℓ E) f
    let eH : (F.mapHomotopyCategory (.up ℤ)).obj (Functor.tensorModelCoefficient B) ≅
      Functor.tensorModelCoefficient B' := (F.mapHomotopyCategoryFactors (.up ℤ)).app
        ((CochainComplex.singleFunctor _ 0).obj B) ≪≫
      (HomotopyCategory.quotient _ (.up ℤ)).mapIso
        ((F.mapCochainComplexSingleFunctor 0).app B ≪≫
          (HomologicalComplex.single _ (.up ℤ) 0).mapIso e)
    let φX := coefficientMap (integralReductionMap ℓ E) X
    let H := residueExchangeReduction ℓ E X ⋙ residueExchangeRestriction ℓ E X
    let εX : DerivedCategory.Qh ⋙ H ⟶
        (tensorLeft B').mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh := by
      unfold H B' residueExchangeOrdinaryCoefficient
        residueExchangeReduction integralReduction residueExchangeRestriction
      exact Mod.tensorPresentationDerivedCounit φX
    let M := DerivedCategory.Qh.obj P
    let a : (residueExchangeUpperStar (integralCoeff ℓ E) f).obj M ⟶
        DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj P) :=
      (residueExchangeUpperStarCounit (integralCoeff ℓ E) f).app P
    (residueExchangeTensorPullIso ℓ E f).hom.app
        ((residueExchangeUpperStar (integralCoeff ℓ E) f).obj M) ≫
      residueExchangeTensorModelTarget ℓ E f P =
      H.map a ≫
      εX.app
        ((F.mapHomotopyCategory (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map
        ((homotopyTensorSingleIso B').inv.app ((F.mapHomotopyCategory (.up ℤ)).obj P) ≫
          eH.inv ▷ (F.mapHomotopyCategory (.up ℤ)).obj P) := by
  dsimp only
  unfold residueExchangeTensorPullIso
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  rw [integralResidue_tensorPullCounit_core ℓ E f P]
  simp only [Iso.hom_inv_id_app_assoc, residueExchangeTensorCounit, id_eq]
end AlgebraicGeometry.ProEtale.CondensedRing
