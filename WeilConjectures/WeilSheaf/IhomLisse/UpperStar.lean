/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.GeometricFrobeniusMate
public import WeilConjectures.WeilSheaf.Fourier
public import WeilConjectures.WeilSheaf.IhomLisse.UpperStarComparison
public import WeilConjectures.WeilSheaf.StalkTensor
public import WeilConjectures.WeilSheaf.StalkUpperStar
public import WeilConjectures.WeilSheaf.UpperStarConstant

/-!
# Pullback of the internal hom out of a lisse Weil sheaf

For a morphism `φ : X ⟶ Y` of `k₀`-schemes, the pullback `φ̄^*` along its base change to the
geometric fibres is strong monoidal, and the exchange isomorphism `φ̄^* ⋙ Fr_X^* ≅ Fr_Y^* ⋙ φ̄^*`
defining the Weil structure of `φ^* F` is monoidal. Hence a pairing of Weil sheaves compatible
with the Weil structures pulls back to a compatible pairing
(`AlgebraicGeometry.ProEtaleWeilSheaf.upperStar_pairing_str`). Applied to the evaluation, this
shows that the comparison `φ^* [A, B] ⟶ [φ^* A, φ^* B]`
(`AlgebraicGeometry.ProEtale.adicUpperStarIhomComparison`) is a morphism of pro-étale Weil
sheaves; it is an isomorphism for `A` lisse, which gives
`AlgebraicGeometry.ProEtaleWeilSheaf.ihomFunctorCompUpperStarIso`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Endofunctor

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
variable (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]

end AlgebraicGeometry.ProEtaleWeilSheaf

namespace CategoryTheory.NatTrans

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]

/-- A composite of monoidal natural isomorphisms is monoidal. -/
lemma isMonoidal_trans_hom {F G H : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal]
    [H.LaxMonoidal] (e₁ : F ≅ G) (e₂ : G ≅ H) (h₁ : IsMonoidal e₁.hom)
    (h₂ : IsMonoidal e₂.hom) : IsMonoidal (e₁ ≪≫ e₂).hom := by
  rw [Iso.trans_hom]
  infer_instance

/-- The inverse of a monoidal natural isomorphism is monoidal. -/
lemma isMonoidal_symm_hom {F G : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal]
    (e : F ≅ G) (h : IsMonoidal e.hom) : IsMonoidal e.symm.hom := by
  rw [Iso.symm_hom]
  infer_instance

/-- A whiskering of a monoidal natural isomorphism is monoidal. -/
lemma isMonoidal_isoWhiskerLeft_hom {E : Type*} [Category E] [MonoidalCategory E]
    (F : C ⥤ D) {G H : D ⥤ E} [F.LaxMonoidal] [G.LaxMonoidal] [H.LaxMonoidal]
    (e : G ≅ H) (h : IsMonoidal e.hom) : IsMonoidal (Functor.isoWhiskerLeft F e).hom := by
  rw [Functor.isoWhiskerLeft_hom]
  infer_instance

/-- A whiskering of a monoidal natural isomorphism is monoidal. -/
lemma isMonoidal_isoWhiskerRight_hom {E : Type*} [Category E] [MonoidalCategory E]
    {F G : C ⥤ D} (H : D ⥤ E) [F.LaxMonoidal] [G.LaxMonoidal] [H.LaxMonoidal]
    (e : F ≅ G) (h : IsMonoidal e.hom) : IsMonoidal (Functor.isoWhiskerRight e H).hom := by
  rw [Functor.isoWhiskerRight_hom]
  infer_instance

end CategoryTheory.NatTrans

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {X Y : Scheme.{u}} (j : X ⟶ Y) (a : X ≅ X) (b : Y ≅ Y)
  (c : a.hom ≫ j = j ≫ b.hom)

/-- The exchange isomorphism `j^* ⋙ (a⁻¹)_* ≅ (b⁻¹)_* ⋙ j^*` is monoidal. -/
instance isMonoidal_upperStarExchangeIso_hom :
    NatTrans.IsMonoidal (upperStarExchangeIso (WeilCoefficients.{u} l) j a b c).hom :=
  NatTrans.isMonoidal_trans_hom _ _
    (NatTrans.isMonoidal_isoWhiskerLeft_hom _ _ (NatTrans.isMonoidal_symm_hom _ inferInstance))
    (NatTrans.isMonoidal_trans_hom _ _ (NatTrans.isMonoidal_symm_hom _ inferInstance)
      (NatTrans.isMonoidal_trans_hom _ _ inferInstance
        (NatTrans.isMonoidal_trans_hom _ _ inferInstance
          (NatTrans.isMonoidal_isoWhiskerRight_hom _ _ inferInstance))))

/-- The components of the exchange isomorphism. -/
lemma upperStarExchangeIso_hom_app (M) :
    (upperStarExchangeIso (WeilCoefficients.{u} l) j a b c).hom.app M =
      (upperStarIsoLowerStarInv (WeilCoefficients.{u} l) a).inv.app
          ((j)^*[WeilCoefficients.{u} l].obj M) ≫
        (upperStarComp _ a.hom j).inv.app M ≫ (upperStarCongr _ c).hom.app M ≫
        (upperStarComp _ j b.hom).hom.app M ≫
        (j)^*[WeilCoefficients.{u} l].map
          ((upperStarIsoLowerStarInv (WeilCoefficients.{u} l) b).hom.app M) := by
  simp only [upperStarExchangeIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]

-- Stated for a variable isomorphism `α`: for `α = upperStarIsoLowerStarInv` the kernel times out
-- comparing the two objects.
private lemma inv_app_adicUpperStar_obj_X
    {P Q : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l) ⥤
      Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)} (α : P ≅ Q)
    (M : AdicSheaf l Y) :
    α.inv.app ((j)^*ᵃ[l].obj M).X = α.inv.app ((j)^*[WeilCoefficients.{u} l].obj M.X) :=
  rfl

/-- The exchange isomorphism of `ℓ`-adic pullbacks is, on underlying sheaves, the exchange
isomorphism `AlgebraicGeometry.ProEtale.upperStarExchangeIso`. Stated for arbitrary `j`, `a`,
`b`: for the geometric Frobenii the kernel times out on the same proof. -/
lemma adicUpperStarExchangeIso_hom_app_hom (M : AdicSheaf l Y) :
    ((Functor.isoWhiskerLeft _ (adicUpperStarIsoLowerStarInv l a).symm ≪≫
      (adicUpperStarComp l _ _).symm ≪≫ adicUpperStarCongr l c ≪≫ adicUpperStarComp l _ _ ≪≫
      Functor.isoWhiskerRight (adicUpperStarIsoLowerStarInv l b) _).hom.app M).hom =
      (upperStarExchangeIso (WeilCoefficients.{u} l) j a b c).hom.app M.X := by
  rw [upperStarExchangeIso_hom_app]
  simp only [Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Mod.comp_hom', adicUpperStar_map_hom,
    adicUpperStarIsoLowerStarInv_inv_app_hom, adicUpperStarIsoLowerStarInv_hom_app_hom,
    adicUpperStarComp_inv_app_hom, adicUpperStarComp_hom_app_hom, adicUpperStarCongr_hom_app_hom]
  rw [inv_app_adicUpperStar_obj_X]

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
variable (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]

variable (k₀ l) in
/-- The exchange isomorphism `φ̄^* ⋙ Fr_X^* ≅ Fr_Y^* ⋙ φ̄^*` of sheaves of `ℚ̄_ℓ`-modules on the
geometric fibres, with `Fr^* = (Fr⁻¹)_*`: the underlying isomorphism of
`AlgebraicGeometry.ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso`. -/
noncomputable abbrev upperStarFrobeniusExchangeIso :
    (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))^*[
        WeilCoefficients.{u} l] ⋙
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[WeilCoefficients.{u} l] ≅
    ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[WeilCoefficients.{u} l] ⋙
      (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))^*[
        WeilCoefficients.{u} l] :=
  upperStarExchangeIso (WeilCoefficients.{u} l)
    (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius
    (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ
      (comp_over φ (Spec (CommRingCat.of k₀)))).symm

/-- The Weil structure of the pullback of a pro-étale Weil sheaf, on underlying sheaves. -/
lemma upperStar_obj_str_hom_hom (P : ProEtaleWeilSheaf k₀ l Y) :
    ((upperStar k₀ l φ).obj P).str.hom.hom =
      (upperStarFrobeniusExchangeIso k₀ l φ).hom.app P.carrier.X ≫
        (Scheme.Hom.geometricFiberMap φ (comp_over φ _))^*[WeilCoefficients.{u} l].map
          P.str.hom.hom := by
  have h1 : ((upperStar k₀ l φ).obj P).str = (adicUpperStarGeometricFiberMapCompFrobeniusIso l φ
      (comp_over φ (Spec (CommRingCat.of k₀)))).app P.carrier ≪≫
        (Scheme.Hom.geometricFiberMap φ (comp_over φ _))^*ᵃ[l].mapIso P.str :=
    IsoAlgebra.mapOfNatIso_obj_str _ P
  rw [h1, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Mod.comp_hom', adicUpperStar_map_hom]
  exact congrArg (· ≫ _) (adicUpperStarExchangeIso_hom_app_hom _ _ _ _ P.carrier)

/-- **Pullbacks of compatible pairings are compatible.** A pairing `e : P ⊗ Q ⟶ R` of the
underlying sheaves of pro-étale Weil sheaves compatible with their Weil structures induces the
compatible pairing `φ̄^* P ⊗ φ̄^* Q ⟶ φ̄^*(P ⊗ Q) ⟶ φ̄^* R`. -/
theorem upperStar_pairing_str (P Q R : ProEtaleWeilSheaf k₀ l Y)
    (e : P.carrier.X ⊗ Q.carrier.X ⟶ R.carrier.X)
    (h : (P.str.hom.hom ⊗ₘ Q.str.hom.hom) ≫ e =
      μ ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[WeilCoefficients.{u} l]
          P.carrier.X Q.carrier.X ≫
        ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[_].map e ≫
          R.str.hom.hom) :
    (((upperStar k₀ l φ).obj P).str.hom.hom ⊗ₘ ((upperStar k₀ l φ).obj Q).str.hom.hom) ≫
        (μ (Scheme.Hom.geometricFiberMap φ (comp_over φ _))^*[WeilCoefficients.{u} l]
          P.carrier.X Q.carrier.X ≫
          (Scheme.Hom.geometricFiberMap φ (comp_over φ _))^*[_].map e) =
      μ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[WeilCoefficients.{u} l]
          ((Scheme.Hom.geometricFiberMap φ (comp_over φ _))^*[_].obj P.carrier.X)
          ((Scheme.Hom.geometricFiberMap φ (comp_over φ _))^*[_].obj Q.carrier.X) ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[_].map
          (μ (Scheme.Hom.geometricFiberMap φ (comp_over φ _))^*[WeilCoefficients.{u} l]
            P.carrier.X Q.carrier.X ≫
            (Scheme.Hom.geometricFiberMap φ (comp_over φ _))^*[_].map e) ≫
          ((upperStar k₀ l φ).obj R).str.hom.hom := by
  have hψ := NatTrans.IsMonoidal.tensor (τ := (upperStarFrobeniusExchangeIso k₀ l φ).hom)
    P.carrier.X Q.carrier.X
  have nψ := (upperStarFrobeniusExchangeIso k₀ l φ).hom.naturality e
  simp only [Functor.LaxMonoidal.comp_μ, Functor.comp_map, Functor.comp_obj] at hψ nψ
  rw [upperStar_obj_str_hom_hom, upperStar_obj_str_hom_hom, upperStar_obj_str_hom_hom,
    ← tensorHom_comp_tensorHom_assoc, μ_natural_assoc, ← Functor.map_comp, h]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hψ, reassoc_of% nψ]

end AlgebraicGeometry.ProEtaleWeilSheaf
