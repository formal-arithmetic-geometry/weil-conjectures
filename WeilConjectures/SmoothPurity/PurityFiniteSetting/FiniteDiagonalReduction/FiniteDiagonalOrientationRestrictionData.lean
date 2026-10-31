/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalReductionComparisons
public import WeilConjectures.AlgebraicGeometry.DualizingLocality.DualizingSigmaCocycleLocality

/-! # Canonical restriction coordinates for the finite diagonal assembly

Source: orientation charts, restriction of exceptional mates and Tate coefficients.
(blueprint: def-pur-finite-diagonal-orientation-restriction-data). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction

variable (P : PurityFiniteSetting.{u})
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable (aY : Y ⟶ Spec (.of P.field.k))
variable [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]

/-- The counit-normalized source and target open restriction, transported from
ordinary etale coordinates. This is an actual composite of exceptional mates and
site/unit comparisons; no orientation is used to define it.
Source: diagonal assembly proof Step 2 and dualizing locality.
(blueprint: def-pur-finite-diagonal-orientation-restriction-data). -/
def affineDualizingRestriction
    (U : X.affineOpens) (V : Y.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :=
  letI := P.noetherian aY
  letI := P.noetherian (f ≫ aY)
  letI := Dnc.compactifiable P f aY
  let h := f.resLE V.1 U.1 hUV
  letI : IsAffine U.1.toScheme := U.2
  letI : IsAffine V.1.toScheme := V.2
  letI : X.Over (Spec (.of P.field.k)) := ⟨f ≫ aY⟩
  letI : Y.Over (Spec (.of P.field.k)) := ⟨aY⟩
  letI : U.1.toScheme.Over (Spec (.of P.field.k)) := ⟨U.1.ι ≫ f ≫ aY⟩
  letI : V.1.toScheme.Over (Spec (.of P.field.k)) := ⟨V.1.ι ≫ aY⟩
  letI : LocallyOfFiniteType (X ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (f ≫ aY))
  letI : QuasiCompact (X ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (f ≫ aY))
  letI : LocallyOfFiniteType (Y ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (aY))
  letI : QuasiCompact (Y ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (aY))
  letI : LocallyOfFiniteType (U.1.toScheme ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (U.1.ι ≫ f ≫ aY))
  letI : QuasiCompact (U.1.toScheme ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (U.1.ι ≫ f ≫ aY))
  letI : LocallyOfFiniteType (V.1.toScheme ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (V.1.ι ≫ aY))
  letI : QuasiCompact (V.1.toScheme ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (V.1.ι ≫ aY))
  letI : f.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  letI : U.1.ι.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  letI : V.1.ι.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  letI : h.IsOver (Spec (.of P.field.k)) := ⟨by
    change h ≫ V.1.ι ≫ aY = U.1.ι ≫ f ≫ aY
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]⟩
  letI := Dnc.compactifiable P h (V.1.ι ≫ aY)
  let R := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
    U.1.ι).leftDerivedFunctor
  let J := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) U.1.toScheme).mapDerivedCategory
  R.mapIso (P.diagonalDualizingComparison f ≪≫
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso
          (P.chartDualizingUnit f)).symm) ≪≫
    Dnc.pullComparison P U.1.ι (Etale.dualizingComplex P.Coefficient f) ≪≫
    J.mapIso (ProEtale.DualizingLocality.restriction P f h U.1.ι V.1.ι
      ⟨(Scheme.Hom.resLE_comp_ι f hUV).symm⟩) ≪≫
    J.mapIso (P.chartDualizingUnit h) ≪≫ (P.diagonalDualizingComparison h).symm

/-- Canonical Tate restriction with the same projective-line trace transport as
vectorFactor, including the empty tensor at rank zero.
Source: diagonal assembly proof Step 3.
(blueprint: def-pur-finite-diagonal-orientation-restriction-data). -/
def affineTateRestriction (d : ℕ) (U : X.affineOpens) :=
  Dnc.pullComparison P U.1.ι (P.diagonalTwistEtale X d) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) U.1.toScheme).mapDerivedCategory.mapIso
      (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates
        (Etale.projectiveLineTraceTransport P.diagonalExponent
          (pow_pos P.coefficients.prime.out.pos P.level)
          P.Coefficient P.diagonalExponent_annihilates)
        U.1.ι (P.diagonalExponent_isUnit (f ≫ aY)) d)

end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
