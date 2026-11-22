/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangeIntegral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangePadicAlgClData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangeProper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeFormalism
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralToPadicAlgClUpperShriekCompatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ToPadicAlgClLowerStarHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.LowerShriekBaseChangeProper
public import WeilConjectures.TraceFormula.IntegersToPadicAlgClLowerStar
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek

/-!
# The coefficient comparisons `𝒪_E ⟶ ℚ̄_ℓ` of `Rf_!`

Write `T = ℚ̄_ℓ ⊗ᴸ_{𝒪_E} -` for the extension of scalars on bounded constructible complexes
(`ProEtale.CondensedRing.boundedConstructibleIntegersToPadicAlgCl`), the composite of the extensions
of scalars along `𝒪_E ⟶ E` and `E ⟶ ℚ̄_ℓ`. This file proves that the comparison
`T Rf_! ≅ Rf_! T` (`ProEtale.CondensedRing.boundedConstructibleLowerShriekIntegersToPadicAlgClIso`)
is compatible with the identification `Rf_! ≅ Rf_*` for a proper `f`
(`ProEtale.CondensedRing.integersToPadicAlgCl_map_lowerShriekIsoLowerStar_inv_app`).

Both coefficient changes `𝒪_E ⟶ E` and `E ⟶ ℚ̄_ℓ` are coefficient changes of the bounded
constructible six functors (`ProEtale.CondensedRing.extendScalarsCoefficientChange`,
`ProEtale.CondensedRing.toPadicAlgClCoefficientChange`), for which the compatibility is
`BoundedConstructibleCoefficientChange.squareCompatible_lowerShriekIsoLowerStar`; the two results
are composed.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace CategoryTheory.NatTrans.SquareCompatible

variable {P₁ Q₁ P₂ Q₂ P₃ Q₃ : Type*} [Category* P₁] [Category* Q₁] [Category* P₂] [Category* Q₂]
  [Category* P₃] [Category* Q₃] {L₁ G₁ : P₁ ⥤ Q₁} {L₂ G₂ : P₂ ⥤ Q₂} {L₃ G₃ : P₃ ⥤ Q₃}
  {T₁ : P₁ ⥤ P₂} {T₁' : Q₁ ⥤ Q₂} {T₂ : P₂ ⥤ P₃} {T₂' : Q₂ ⥤ Q₃}

/-- Isomorphisms `e₁`, `e₂`, `e₃` compatible with two successive changes of coefficients are
compatible with the composite change of coefficients, read on the inverses. -/
lemma inv_app_comp_of_comp {e₁ : L₁ ≅ G₁} {e₂ : L₂ ≅ G₂} {e₃ : L₃ ≅ G₃}
    {S₁ : L₁ ⋙ T₁' ≅ T₁ ⋙ L₂} {U₁ : G₁ ⋙ T₁' ≅ T₁ ⋙ G₂} {S₂ : L₂ ⋙ T₂' ≅ T₂ ⋙ L₃}
    {U₂ : G₂ ⋙ T₂' ≅ T₂ ⋙ G₃} (h₁ : SquareCompatible S₁ U₁ e₁.hom e₂.hom)
    (h₂ : SquareCompatible S₂ U₂ e₂.hom e₃.hom) (M : P₁) :
    T₂'.map (T₁'.map (e₁.inv.app M)) ≫ T₂'.map (S₁.hom.app M) ≫ S₂.hom.app (T₁.obj M) =
      (T₂'.map (U₁.hom.app M) ≫ U₂.hom.app (T₁.obj M)) ≫ e₃.inv.app (T₂.obj (T₁.obj M)) := by
  have k₁ := h₁ M
  have k₂ := h₂ (T₁.obj M)
  simp only [Functor.comp_obj] at k₁ k₂
  rw [← cancel_mono (e₃.hom.app (T₂.obj (T₁.obj M)))]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [← k₂, ← T₂'.map_comp_assoc, ← T₂'.map_comp_assoc, Category.assoc, ← k₁,
    ← T₁'.map_comp_assoc, Iso.inv_hom_id_app, T₁'.map_id, Category.id_comp]
  exact congrArg (_ ≫ ·) (Category.comp_id (U₂.hom.app (T₁.obj M))).symm

end CategoryTheory.NatTrans.SquareCompatible

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The isomorphism `Rp_! ≅ Rp_*` on bounded constructible `ℚ̄_ℓ`-complexes for a proper `p` is the
one of the pushforward datum of `ℚ̄_ℓ`. -/
lemma boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_eq_pushforwardData (p : X ⟶ Y)
    [IsProper p.left] :
    boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ p =
      BoundedConstructiblePushforwardData.lowerShriekIsoLowerStar
        (isIsoRefinementPushforward_padicAlgClPushforwardData ℓ k) p := by
  rw [boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_eq,
    ← boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl_eq']
  unfold boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl
  rfl

variable (k) in
/-- `Rp_! ≅ Rp_*` is compatible with the coefficient comparisons of `𝒪_E ⟶ E`. -/
lemma squareCompatible_lowerShriekIsoLowerStar_extendScalars (p : X ⟶ Y) [IsProper p.left] :
    NatTrans.SquareCompatible (boundedConstructibleLowerShriekExtendScalarsIso ℓ E p)
      (boundedConstructibleLowerStarExtendScalarsIso ℓ E p)
      (boundedConstructibleLowerShriekIsoLowerStar_padicIntegers ℓ E.1 p).hom
      (BoundedConstructiblePushforwardData.lowerShriekIsoLowerStar
        (isIsoRefinementPushforward_continuousMapPushforwardData ℓ k E) p).hom := by
  rw [boundedConstructibleLowerShriekExtendScalarsIso_eq_shriekOfCompactification ℓ E k,
    boundedConstructibleLowerShriekIsoLowerStar_padicIntegers_eq_pushforwardData]
  exact (extendScalarsCoefficientChange ℓ E k).squareCompatible_lowerShriekIsoLowerStar
    (T₀ := fun X ↦ boundedConstructibleExtendScalars X ℓ E) _ _ p rfl

variable (k) in
/-- `Rp_! ≅ Rp_*` is compatible with the coefficient comparisons of `E ⟶ ℚ̄_ℓ`. -/
lemma squareCompatible_lowerShriekIsoLowerStar_toPadicAlgCl (p : X ⟶ Y) [IsProper p.left] :
    NatTrans.SquareCompatible (boundedConstructibleLowerShriekToPadicAlgClIso ℓ E p)
      (boundedConstructibleLowerStarToPadicAlgClIso ℓ E p)
      (BoundedConstructiblePushforwardData.lowerShriekIsoLowerStar
        (isIsoRefinementPushforward_continuousMapPushforwardData ℓ k E) p).hom
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ p).hom := by
  rw [boundedConstructibleLowerShriekToPadicAlgClIso_eq_shriekOfCompactification ℓ E k,
    boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_eq_pushforwardData]
  exact (toPadicAlgClCoefficientChange ℓ E k).squareCompatible_lowerShriekIsoLowerStar
    (T₀ := fun X ↦ boundedConstructibleToPadicAlgCl X ℓ E) _ _ p rfl

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

lemma boundedConstructibleLowerShriekIntegersToPadicAlgClIso_inv_app (f : Y ⟶ X)
    (M : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    (boundedConstructibleLowerShriekIntegersToPadicAlgClIso ℓ E f).inv.app M =
      (boundedConstructibleToPadicAlgCl X.left ℓ E).map
          ((boundedConstructibleLowerShriekExtendScalarsIso ℓ E f).hom.app M) ≫
        (boundedConstructibleLowerShriekToPadicAlgClIso ℓ E f).hom.app
          ((boundedConstructibleExtendScalars Y.left ℓ E).obj M) := by
  simp [boundedConstructibleLowerShriekIntegersToPadicAlgClIso, Functor.isoHComp]

lemma boundedConstructibleLowerStarIntegersToPadicAlgClIso_hom_app (f : Y ⟶ X)
    (M : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    (boundedConstructibleLowerStarIntegersToPadicAlgClIso ℓ E f).hom.app M =
      (boundedConstructibleToPadicAlgCl X.left ℓ E).map
          ((boundedConstructibleLowerStarExtendScalarsIso ℓ E f).hom.app M) ≫
        (boundedConstructibleLowerStarToPadicAlgClIsoOfQcqs ℓ E f).hom.app
          ((boundedConstructibleExtendScalars Y.left ℓ E).obj M) := by
  simp [boundedConstructibleLowerStarIntegersToPadicAlgClIso]
  rfl

/-- **`Rh_! ≅ Rh_*` commutes with the coefficient comparisons** for a proper `h`: the
comparison `T Rh_! ≅ Rh_! T` corresponds to the comparison `T Rh_* ≅ Rh_* T` under the
identifications `Rh_! ≅ Rh_*` over `𝒪_E` and over `ℚ̄_ℓ`. -/
theorem integersToPadicAlgCl_map_lowerShriekIsoLowerStar_inv_app (h : Y ⟶ X) [IsProper h.left]
    (M : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    (boundedConstructibleIntegersToPadicAlgCl ℓ E X).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicIntegers ℓ E.1 h).inv.app M) ≫
        (boundedConstructibleLowerShriekIntegersToPadicAlgClIso ℓ E h).inv.app M =
      (boundedConstructibleLowerStarIntegersToPadicAlgClIso ℓ E h).hom.app M ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ h).inv.app
          ((boundedConstructibleIntegersToPadicAlgCl ℓ E Y).obj M) := by
  have e₁ := boundedConstructibleLowerShriekIntegersToPadicAlgClIso_inv_app ℓ E h M
  have e₂ := boundedConstructibleLowerStarIntegersToPadicAlgClIso_hom_app ℓ E h M
  have e₃ := boundedConstructibleLowerStarToPadicAlgClIsoOfQcqs_eq ℓ E h
  have H := NatTrans.SquareCompatible.inv_app_comp_of_comp
    (squareCompatible_lowerShriekIsoLowerStar_extendScalars ℓ E k h)
    (squareCompatible_lowerShriekIsoLowerStar_toPadicAlgCl ℓ E k h) M
  have e₄ := e₂.trans (congrArg (fun e ↦ _ ≫ e.hom.app
    ((boundedConstructibleExtendScalars Y.left ℓ E).obj M)) e₃)
  exact (congrArg (_ ≫ ·) e₁).trans (H.trans (congrArg (· ≫ _) e₄.symm))

end AlgebraicGeometry.ProEtale.CondensedRing
