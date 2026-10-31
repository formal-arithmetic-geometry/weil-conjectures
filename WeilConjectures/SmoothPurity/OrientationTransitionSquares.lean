/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SmoothPurity.OrientationTransitionFrame
public import WeilConjectures.SmoothPurity.OrientationTransitionUnit
public import WeilConjectures.SmoothPurity.OrientationFinite
public import WeilConjectures.SmoothPurity.OrientationTransitionUpperShriek

/-!
# The constituents of the finite orientations under the reduction of coefficients

Let `f : X ⟶ Y` be a morphism of separated `k`-schemes of finite type which is smooth of pure
relative dimension `d`, and `Ψ` the derived extension of scalars along
`Λ = 𝒪_E ⧸ ℓⁿ⁺² ⟶ Λ' = 𝒪_E ⧸ ℓⁿ⁺¹`. This file proves the formal part of the compatibility of
the canonical finite orientations `θₘ` (`ProEtale.CondensedRing.etaleReductionSmoothOrientationIso`)
with `Ψ`: `ProEtale.CondensedRing.map_etaleReductionSmoothOrientationIso_hom_comp_of` deduces it
from the compatibility of its three constituents, and states the compatibility of the reduction
of the Tate twist (`ProEtale.CondensedRing.map_etaleReductionIntegralTateTwistIso_comp`).
-/

@[expose] public section


universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [NeZero (ℓ : k)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (E : PadicAlgCl.FiniteIntermediateField ℓ) (f : X ⟶ Y) (d : ℕ)
  [SmoothOfRelativeDimension d f.left]

/-- The canonical Tate data of the reduction `𝒪_E ⧸ ℓⁿ⁺² ⟶ 𝒪_E ⧸ ℓⁿ⁺¹`
(`Etale.reductionTateTwistShiftData`, for the `ℓ`-th power map on the roots of unity). -/
noncomputable abbrev integersModPowTateShiftData (n : ℕ) :=
  Etale.reductionTateTwistShiftData (integersModPowCoeffTransition_surjective ℓ E.1 (n + 1))
    (ker_integersModPowCoeffTransition ℓ E.1 (n + 1)) ℓ
    (ringChar_integersModPowCoeff_succ ℓ E.1 (n + 1))

/-- The reduction `𝒪_E ⧸ ℓⁿ⁺² ⟶ 𝒪_E ⧸ ℓⁿ⁺¹` as a change of coefficients with supports. -/
noncomputable abbrev integersModPowSupportedCoefficientChange (n : ℕ) :=
  Etale.reductionSupportedCoefficientChange (integersModPowCoeffTransition_surjective ℓ E.1 (n + 1))
    (ker_integersModPowCoeffTransition ℓ E.1 (n + 1)) (integersModPowTateShiftData ℓ E n)

/-- A formal pasting: if `F` carries `S₂`, `D₂` and `V₂` to `S₁`, `D₁` and `V₁` through `t`, `ω`
and `w`, then it carries `S₂ ≫ D₂⁻¹ ≫ V₂⁻¹` to `S₁ ≫ D₁⁻¹ ≫ V₁⁻¹`. -/
lemma Functor.map_comp_inv_comp_inv_comp_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {a b c e : C} {b' c' e' p q : D} (S₂ : a ⟶ b) (D₂ : c ≅ b) (V₂ : e ≅ c)
    (w : F.obj e ⟶ e') (p₁ : F.obj a ⟶ p) (p₂ : p ⟶ q) (S₁ : q ⟶ b') (D₁ : c' ≅ b')
    (V₁ : e' ≅ c') (t : F.obj b ⟶ b') (ω : F.obj c ⟶ c') [IsIso ω]
    (hT : F.map S₂ ≫ t = p₁ ≫ p₂ ≫ S₁) (hD : F.map D₂.hom ≫ t = ω ≫ D₁.hom)
    (hW : F.map V₂.hom ≫ ω = w ≫ V₁.hom) :
    F.map (S₂ ≫ D₂.inv ≫ V₂.inv) ≫ w = p₁ ≫ p₂ ≫ S₁ ≫ D₁.inv ≫ V₁.inv := by
  have hD' : F.map D₂.inv = t ≫ D₁.inv ≫ inv ω := by
    rw [← cancel_epi (F.map D₂.hom), ← F.map_comp, D₂.hom_inv_id, F.map_id, reassoc_of% hD,
      D₁.hom_inv_id_assoc, IsIso.hom_inv_id]
  have hW' : F.map V₂.inv ≫ w = ω ≫ V₁.inv := by
    rw [← cancel_epi (F.map V₂.hom), ← F.map_comp_assoc, V₂.hom_inv_id, F.map_id,
      Category.id_comp, reassoc_of% hW, V₁.hom_inv_id, Category.comp_id]
  simp only [F.map_comp, Category.assoc, hW', hD', IsIso.inv_hom_id_assoc, reassoc_of% hT]

/-- **The compatibility of the finite orientations with the reduction, from its three
constituents.** Write `θₘ` for the canonical finite orientation
(`etaleReductionSmoothOrientationIso`), built from the reduction of the Tate twist, the diagonal
orientation `Dₘ : ω_f ≅ Λ_X(d)[2d]` (`Etale.dualizingComplexTwistShiftIso`) and the reduction of
`Rf^! 𝒪` (`etaleReductionUpperShriekIso`, `etaleReductionUnitIso`). Given identifications
`tsc : Ψ(Λ_X(d)[2d]) ≅ Λ'_X(d)[2d]` and `vω : Ψ ω_f ⟶ ω'_f` such that the three constituents
are compatible with `β` (`hT`, `hW`) and `Ψ D_{n+2}` is `D_{n+1}` (`hD`), `Ψ θ_{n+2}` is
`θ_{n+1}` through `β`. -/
theorem map_etaleReductionSmoothOrientationIso_hom_comp_of (n : ℕ)
    [HasCompactification f.left]
    [HasInvertibleExponent (integersModPowCoeff.{u} ℓ E.1 (n + 1 + 1)) X.left]
    [HasInvertibleExponent (integersModPowCoeff.{u} ℓ E.1 (n + 1 + 1)) Y.left]
    [HasInvertibleExponent (integersModPowCoeff.{u} ℓ E.1 (n + 1)) X.left]
    [HasInvertibleExponent (integersModPowCoeff.{u} ℓ E.1 (n + 1)) Y.left]
    (tsc : (integersModPowDerivedExtendScalars ℓ E.1 (n + 1) X.left).obj
        ((Etale.twistShift (integersModPowCoeff.{u} ℓ E.1 (n + 1 + 1)) X.left d).obj
          (Etale.constantComplex _ X.left)) ≅
      (Etale.twistShift (integersModPowCoeff.{u} ℓ E.1 (n + 1)) X.left d).obj
          (Etale.constantComplex _ X.left))
    (vω : (integersModPowDerivedExtendScalars ℓ E.1 (n + 1) X.left).obj
        (Etale.dualizingComplex (integersModPowCoeff.{u} ℓ E.1 (n + 1 + 1)) f.left) ⟶
      Etale.dualizingComplex (integersModPowCoeff.{u} ℓ E.1 (n + 1)) f.left) [IsIso vω]
    (hT : (integersModPowDerivedExtendScalars ℓ E.1 (n + 1) X.left).map
          ((shiftFunctor _ (2 * d : ℤ)).map
            (etaleReductionIntegralTateTwistIso ℓ E.1 (n + 1 + 1) X d ≪≫ (λ_ _).symm).hom) ≫
        tsc.hom =
      ((integersModPowDerivedExtendScalars ℓ E.1 (n + 1) X.left).commShiftIso
          (2 * d : ℤ)).hom.app _ ≫
        (etaleReductionExtendScalarsIsoApp ℓ E.1 (n + 1) X _).hom⟦(2 * d : ℤ)⟧' ≫
          (shiftFunctor _ (2 * d : ℤ)).map
            (etaleReductionIntegralTateTwistIso ℓ E.1 (n + 1) X d ≪≫ (λ_ _).symm).hom)
    (hD : (integersModPowDerivedExtendScalars ℓ E.1 (n + 1) X.left).map
          (Etale.dualizingComplexTwistShiftIso (integersModPowCoeff.{u} ℓ E.1 (n + 1 + 1))
            f.left d Y.hom).hom ≫ tsc.hom =
      vω ≫ (Etale.dualizingComplexTwistShiftIso (integersModPowCoeff.{u} ℓ E.1 (n + 1))
            f.left d Y.hom).hom)
    (hW : (integersModPowDerivedExtendScalars ℓ E.1 (n + 1) X.left).map
          ((etaleReductionUpperShriekIso ℓ E.1 (n + 1 + 1) f).app (𝟙_ _) ≪≫
            (Etale.rightDerivedUpperShriek (integersModPowCoeff.{u} ℓ E.1 (n + 1 + 1))
              f.left).mapIso (etaleReductionUnitIso ℓ E.1 (n + 1 + 1) Y)).hom ≫ vω =
      (etaleReductionExtendScalarsIsoApp ℓ E.1 (n + 1) X _).hom ≫
        ((etaleReductionUpperShriekIso ℓ E.1 (n + 1) f).app (𝟙_ _) ≪≫
          (Etale.rightDerivedUpperShriek (integersModPowCoeff.{u} ℓ E.1 (n + 1))
            f.left).mapIso (etaleReductionUnitIso ℓ E.1 (n + 1) Y)).hom) :
    (integersModPowDerivedExtendScalars ℓ E.1 (n + 1) X.left).map
        (etaleReductionSmoothOrientationIso ℓ E f d (n + 1 + 1)).hom ≫
      (etaleReductionExtendScalarsIsoApp ℓ E.1 (n + 1) X _).hom =
    ((integersModPowDerivedExtendScalars ℓ E.1 (n + 1) X.left).commShiftIso (2 * d : ℤ)).hom.app _ ≫
      (etaleReductionExtendScalarsIsoApp ℓ E.1 (n + 1) X _).hom⟦(2 * d : ℤ)⟧' ≫
        (etaleReductionSmoothOrientationIso ℓ E f d (n + 1)).hom := by
  exact Functor.map_comp_inv_comp_inv_comp_eq _ _
    (Etale.dualizingComplexTwistShiftIso (integersModPowCoeff.{u} ℓ E.1 (n + 1 + 1)) f.left d
      Y.hom)
    ((etaleReductionUpperShriekIso ℓ E.1 (n + 1 + 1) f).app (𝟙_ _) ≪≫
      (Etale.rightDerivedUpperShriek (integersModPowCoeff.{u} ℓ E.1 (n + 1 + 1))
        f.left).mapIso (etaleReductionUnitIso ℓ E.1 (n + 1 + 1) Y)) _ _ _ _
    (Etale.dualizingComplexTwistShiftIso (integersModPowCoeff.{u} ℓ E.1 (n + 1)) f.left d Y.hom)
    ((etaleReductionUpperShriekIso ℓ E.1 (n + 1) f).app (𝟙_ _) ≪≫
      (Etale.rightDerivedUpperShriek (integersModPowCoeff.{u} ℓ E.1 (n + 1))
        f.left).mapIso (etaleReductionUnitIso ℓ E.1 (n + 1) Y)) tsc.hom vω hT hD hW

end AlgebraicGeometry.ProEtale.CondensedRing
