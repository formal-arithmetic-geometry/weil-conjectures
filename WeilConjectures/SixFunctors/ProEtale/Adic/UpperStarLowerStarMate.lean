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

omit [Fact l.Prime] in
/-- `unit_mateEquiv` for a known mate `γ`, at an explicit object. Stated for general
adjunctions: instantiating `unit_mateEquiv` directly produces objects `(𝟭 _).obj M` which the
kernel cannot compare with `M` inside pro-étale exchange isomorphisms. -/
private lemma unit_app_comp_app_of_mateEquiv_eq {C D E F : Type*} [Category* C] [Category* D]
    [Category* E] [Category* F] {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ : E ⥤ F} {R₂ : F ⥤ E} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : TwoSquare G L₁ L₂ H)
    (γ : TwoSquare R₁ H G R₂) (h : mateEquiv adj₁ adj₂ α = γ) (c : C) :
    G.map (adj₁.unit.app c) ≫ γ.app (L₁.obj c) = adj₂.unit.app (G.obj c) ≫ R₂.map (α.app c) :=
  h ▸ unit_mateEquiv adj₁ adj₂ α c

/-- The unit of the `ℓ`-adic adjunction `φ^* ⊣ φ_*` is that of the underlying sheaves. -/
private lemma adicUnit_app_hom (M : AdicSheaf l Y) :
    ((adicUpperStarLowerStarAdjunction l φ).unit.app M).hom =
      (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) φ).unit.app M.X := by
  rw [adicUpperStarLowerStarAdjunction, Adjunction.modAdjunction_unit_app_hom]

/-- The pushforward of the `ℓ`-adic unit is that of the underlying unit. -/
private lemma lowerStar_map_adicUnit_app_hom (M : AdicSheaf l Y) :
    ((b.inv)_*ᵃ[l].map ((adicUpperStarLowerStarAdjunction l φ).unit.app M)).hom =
      (b.inv)_*[_].map ((upperStarLowerStarAdjunction (WeilCoefficients.{u} l) φ).unit.app
        M.X) := by
  rw [adicLowerStar_map_hom, adicUnit_app_hom]

/-- The `ℓ`-adic unit at `(b⁻¹)_* M` is the underlying unit at `(b⁻¹)_* M.X`. -/
private lemma adicUnit_app_lowerStar_obj_hom (M : AdicSheaf l Y) :
    ((adicUpperStarLowerStarAdjunction l φ).unit.app ((b.inv)_*ᵃ[l].obj M)).hom =
      (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) φ).unit.app
        ((b.inv)_*[_].obj M.X) :=
  adicUnit_app_hom φ _

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
  have h := unit_app_comp_app_of_mateEquiv_eq
    (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) φ) (upperStarLowerStarAdjunction _ φ)
    (TwoSquare.mk _ _ _ _ (upperStarExchangeIso (WeilCoefficients.{u} l) φ a b c).inv) _
    (mateEquiv_upperStarExchangeIso_inv _ φ a b w c) M.X
  have h₁ : ((φ)_*ᵃ[l].map (E.inv.app M)).hom =
      (φ)_*[_].map ((upperStarExchangeIso (WeilCoefficients.{u} l) φ a b c).inv.app M.X) := by
    rw [adicLowerStar_map_hom, hE]
  rw [Mod.comp_hom', Mod.comp_hom']
  exact (congrArg₂ (· ≫ ·) (lowerStar_map_adicUnit_app_hom φ b M) (hE' _)).trans
    (h.trans (congrArg₂ (· ≫ ·) (adicUnit_app_lowerStar_obj_hom φ b M) h₁).symm)

section GeometricFrobenius

variable {k : Type u} [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}} {f : X₀ ⟶ Spec (.of k)}
  {g : Y₀ ⟶ Spec (.of k)} (ψ : X₀ ⟶ Y₀) (hψ : ψ ≫ g = f)

/-- Unfolding the `ℓ`-adic pullback exchange isomorphism of the geometric Frobenius. -/
private lemma adicUpperStarGeometricFiberMapCompFrobeniusIso_eq' :
    adicUpperStarGeometricFiberMapCompFrobeniusIso l ψ hψ =
      Functor.isoWhiskerLeft _ (adicUpperStarIsoLowerStarInv l f.geometricGaloisFrobenius).symm ≪≫
      (adicUpperStarComp l _ _).symm ≪≫
      adicUpperStarCongr l (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius ψ hψ).symm ≪≫
      adicUpperStarComp l _ _ ≪≫
      Functor.isoWhiskerRight (adicUpperStarIsoLowerStarInv l g.geometricGaloisFrobenius) _ :=
  rfl

/-- Unfolding the `ℓ`-adic pushforward exchange isomorphism of the geometric Frobenius. -/
private lemma adicLowerStarGeometricFiberMapCompFrobeniusIso_eq :
    adicLowerStarGeometricFiberMapCompFrobeniusIso l ψ hψ =
      adicLowerStarComp l _ _ ≪≫
        adicLowerStarCongr l
          (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv ψ hψ) ≪≫
        (adicLowerStarComp l _ _).symm :=
  rfl

/-- **The `ℓ`-adic Frobenius exchange isomorphisms of `φ̄^*` and `φ̄_*` are mates** under the
adjunction `φ̄^* ⊣ φ̄_*`, for the base change `φ̄` of a morphism `φ` of schemes over a finite
field. Consequently the unit and the counit of `φ̄^* ⊣ φ̄_*` are compatible with the Weil
structures. -/
lemma mateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv :
    mateEquiv (adicUpperStarLowerStarAdjunction l (Scheme.Hom.geometricFiberMap ψ hψ))
        (adicUpperStarLowerStarAdjunction l (Scheme.Hom.geometricFiberMap ψ hψ))
        (TwoSquare.mk _ _ _ _ (adicUpperStarGeometricFiberMapCompFrobeniusIso l ψ hψ).inv) =
      TwoSquare.mk _ _ _ _ (adicLowerStarGeometricFiberMapCompFrobeniusIso l ψ hψ).hom := by
  rw [adicUpperStarGeometricFiberMapCompFrobeniusIso_eq',
    adicLowerStarGeometricFiberMapCompFrobeniusIso_eq]
  exact mateEquiv_eq_of_hom_app_hom _ _ _
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv ψ hψ)
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius ψ hψ).symm
    (adicUpperStarExchangeIso_inv_app_hom _ _ _ _) (adicLowerStarExchangeIso_hom_app_hom _ _ _ _)

end GeometricFrobenius

end AlgebraicGeometry.ProEtale
