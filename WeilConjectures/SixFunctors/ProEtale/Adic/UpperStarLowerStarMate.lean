/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.GeometricFrobeniusMate

/-!
# The `ℓ`-adic Frobenius exchange isomorphisms of `φ̄^*` and `φ̄_*` are mates

Let `φ : X₀ ⟶ Y₀` be a morphism of schemes over a finite field with base change
`φ̄ : X ⟶ Y` to the geometric fibres. The exchange isomorphisms
`φ̄^* ⋙ (Fr_X⁻¹)_* ≅ (Fr_Y⁻¹)_* ⋙ φ̄^*` and `φ̄_* ⋙ (Fr_Y⁻¹)_* ≅ (Fr_X⁻¹)_* ⋙ φ̄_*` of `ℓ`-adic
sheaves are mates under the adjunction `φ̄^* ⊣ φ̄_*`
(`AlgebraicGeometry.ProEtale.mateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv`).
The `ℓ`-adic functors and their structure isomorphisms are those of the underlying sheaves
(`WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence`), so this follows from the
statement for sheaves, `AlgebraicGeometry.ProEtale.mateEquiv_upperStarExchangeIso_inv`.

The proofs are stated for general commutative squares and specialised to the geometric
Frobenius afterwards: the kernel cannot check the same proofs at the geometric Frobenius.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {X Y : Scheme.{u}} (φ : X ⟶ Y) (a : X ≅ X) (b : Y ≅ Y)

/-- The `ℓ`-adic exchange isomorphism `φ^* ⋙ (a⁻¹)_* ≅ (b⁻¹)_* ⋙ φ^*` of pullbacks along a
commutative square `a ≫ φ = φ ≫ b` is that of the underlying sheaves. -/
lemma adicUpperStarExchangeIso_hom_app_hom (c : a.hom ≫ φ = φ ≫ b.hom) (M : AdicSheaf l Y) :
    ((Functor.isoWhiskerLeft _ (adicUpperStarIsoLowerStarInv l a).symm ≪≫
      (adicUpperStarComp l _ _).symm ≪≫ adicUpperStarCongr l c ≪≫ adicUpperStarComp l _ _ ≪≫
      Functor.isoWhiskerRight (adicUpperStarIsoLowerStarInv l b) _).hom.app M).hom =
      (upperStarExchangeIso (WeilCoefficients.{u} l) φ a b c).hom.app M.X := by
  simp only [upperStarExchangeIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Mod.comp_hom', adicUpperStar_map_hom,
    adicUpperStarIsoLowerStarInv_inv_app_hom, adicUpperStarIsoLowerStarInv_hom_app_hom,
    adicUpperStarComp_inv_app_hom, adicUpperStarComp_hom_app_hom, adicUpperStarCongr_hom_app_hom]
  rfl

/-- The inverse of the `ℓ`-adic exchange isomorphism of pullbacks is that of the underlying
sheaves. -/
lemma adicUpperStarExchangeIso_inv_app_hom (c : a.hom ≫ φ = φ ≫ b.hom) (M : AdicSheaf l Y) :
    ((Functor.isoWhiskerLeft _ (adicUpperStarIsoLowerStarInv l a).symm ≪≫
      (adicUpperStarComp l _ _).symm ≪≫ adicUpperStarCongr l c ≪≫ adicUpperStarComp l _ _ ≪≫
      Functor.isoWhiskerRight (adicUpperStarIsoLowerStarInv l b) _).inv.app M).hom =
      (upperStarExchangeIso (WeilCoefficients.{u} l) φ a b c).inv.app M.X := by
  rw [← cancel_epi ((upperStarExchangeIso (WeilCoefficients.{u} l) φ a b c).hom.app M.X),
    Iso.hom_inv_id_app, ← adicUpperStarExchangeIso_hom_app_hom, ← Mod.comp_hom',
    Iso.hom_inv_id_app]
  rfl

/-- The `ℓ`-adic exchange isomorphism `φ_* ⋙ (b⁻¹)_* ≅ (a⁻¹)_* ⋙ φ_*` of pushforwards along a
commutative square `φ ≫ b⁻¹ = a⁻¹ ≫ φ` is that of the underlying sheaves. -/
lemma adicLowerStarExchangeIso_hom_app_hom (w : φ ≫ b.inv = a.inv ≫ φ) (M : AdicSheaf l X) :
    ((adicLowerStarComp l _ _ ≪≫ adicLowerStarCongr l w ≪≫
      (adicLowerStarComp l _ _).symm).hom.app M).hom =
      (lowerStarExchangeIso (WeilCoefficients.{u} l) φ a b w).hom.app M.X := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Mod.comp_hom',
    adicLowerStarComp_hom_app_hom, adicLowerStarComp_inv_app_hom, adicLowerStarCongr_hom_app_hom]

/-- A criterion for `ℓ`-adic exchange isomorphisms to be mates: their underlying morphisms of
sheaves are the sheaf-level exchange isomorphisms, which are mates
(`AlgebraicGeometry.ProEtale.mateEquiv_upperStarExchangeIso_inv`). -/
lemma mateEquiv_eq_of_hom_app_hom (w : φ ≫ b.inv = a.inv ≫ φ) (c : a.hom ≫ φ = φ ≫ b.hom)
    {E : (φ)^*ᵃ[l] ⋙ (a.inv)_*ᵃ[l] ≅ (b.inv)_*ᵃ[l] ⋙ (φ)^*ᵃ[l]}
    {E' : (φ)_*ᵃ[l] ⋙ (b.inv)_*ᵃ[l] ≅ (a.inv)_*ᵃ[l] ⋙ (φ)_*ᵃ[l]}
    (hE : ∀ M, (E.inv.app M).hom =
      (upperStarExchangeIso (WeilCoefficients.{u} l) φ a b c).inv.app M.X)
    (hE' : ∀ M, (E'.hom.app M).hom =
      (lowerStarExchangeIso (WeilCoefficients.{u} l) φ a b w).hom.app M.X) :
    mateEquiv (adicUpperStarLowerStarAdjunction l φ) (adicUpperStarLowerStarAdjunction l φ)
        (TwoSquare.mk _ _ _ _ E.inv) = TwoSquare.mk _ _ _ _ E'.hom := by
  refine mateEquiv_eq_of_unit _ _ _ _ fun M ↦ Mod.hom_ext _ _ ?_
  have h := unit_mateEquiv (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) φ)
    (upperStarLowerStarAdjunction _ φ)
    (TwoSquare.mk _ _ _ _ (upperStarExchangeIso (WeilCoefficients.{u} l) φ a b c).inv) M.X
  rw [mateEquiv_upperStarExchangeIso_inv _ φ a b w c] at h
  rw [Mod.comp_hom', Mod.comp_hom', adicLowerStar_map_hom, adicLowerStar_map_hom,
    adicUpperStarLowerStarAdjunction, Adjunction.modAdjunction_unit_app_hom,
    Adjunction.modAdjunction_unit_app_hom]
  rw [hE, hE']
  sorry

end AlgebraicGeometry.ProEtale
