/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.UpperStarComp
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Coherence
public import WeilConjectures.WeilSheaf.StalkFunctor

/-!
# Geometric stalks of a pullback of Weil sheaves

Let `φ : X' ⟶ X` be a morphism of `k₀`-schemes and `F` a Weil sheaf on `X`. For a geometric
point `s` of `X̄'` with `s ≫ Frᵐ = σᵐ ≫ s`, the stalk of `φ^* F` at `s` is the stalk of `F` at
`s ≫ φ̄`, with the same Frobenius.

The iterated Weil structure `φ_m : (Frᵐ)^* F ≅ F` is defined through pushforwards along the
inverse Frobenius (`AlgebraicGeometry.WeilSheaf.frobeniusPowIso`). Its pullback form
`AlgebraicGeometry.WeilSheaf.frobeniusPowUpperStarIso` satisfies the recursion
`AlgebraicGeometry.WeilSheaf.frobeniusPowUpperStarIso_succ`, by the coherence of the
identification `e^* ≅ (e⁻¹)_*` with composition (`ProEtale.upperStarIsoLowerStarInv_trans`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry.WeilSheaf

open scoped AlgebraicGeometry.ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The iterated Weil structure of a Weil sheaf in pullback form,
`(Frᵐ)^* F ≅ (Fr⁻ᵐ)_* F ≅ F`. -/
noncomputable def frobeniusPowUpperStarIso (F : WeilSheaf k₀ l X) (m : ℕ) :
    ((((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom)^*[
      WeilCoefficients.{u} l]).obj
        F.obj.carrier.X ≅ F.obj.carrier.X :=
  (ProEtale.upperStarIsoLowerStarInv _ _).app _ ≪≫
    (ProEtale.AdicSheaf.forget _).mapIso (F.frobeniusPowIso m)

/-- The Weil structure of a Weil sheaf in pullback form, `Fr^* F ≅ (Fr⁻¹)_* F ≅ F`. -/
noncomputable def frobeniusUpperStarIso (F : WeilSheaf k₀ l X) :
    (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[WeilCoefficients.{u} l]).obj
        F.obj.carrier.X ≅ F.obj.carrier.X :=
  (ProEtale.upperStarIsoLowerStarInv _ _).app _ ≪≫
    (ProEtale.AdicSheaf.forget _).mapIso F.obj.str

lemma stalkObjFrobeniusPowIso_eq_upperStar (F : WeilSheaf k₀ l X) (m : ℕ)
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    F.stalkObjFrobeniusPowIso m s = (Sheaf.Γ _ _).mapIso
      ((ProEtale.upperStarComp _ s _).app F.obj.carrier.X ≪≫
        (s)^*[_].mapIso (F.frobeniusPowUpperStarIso m)) :=
  rfl

lemma geometricGaloisFrobenius_pow_succ_hom (m : ℕ) :
    (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (m + 1)).hom) =
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom := by
  rw [pow_succ, Aut.Aut_mul_def, Iso.trans_hom]

/-- The recursion for the iterated Weil structure in pullback form:
`(Fr^{m+1})^* F = Fr^* (Frᵐ)^* F ≅ Fr^* F ≅ F`. -/
lemma frobeniusPowUpperStarIso_succ (F : WeilSheaf k₀ l X) (m : ℕ) :
    F.frobeniusPowUpperStarIso (m + 1) =
      (ProEtale.upperStarCongr _ (geometricGaloisFrobenius_pow_succ_hom m)).app _ ≪≫
        (ProEtale.upperStarComp _ _ _).app _ ≪≫
        (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[_]).mapIso
          (F.frobeniusPowUpperStarIso m) ≪≫ F.frobeniusUpperStarIso := by
  have hE : (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (m + 1) =
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ≪≫
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m := by
    rw [pow_succ, Aut.Aut_mul_def]
  have h1 := congr_app (congrArg Iso.hom
    (ProEtale.upperStarIsoLowerStarInv_congr (WeilCoefficients.{u} l) hE)) F.obj.carrier.X
  have h2 := congr_app (congrArg Iso.hom (ProEtale.upperStarIsoLowerStarInv_trans
    (WeilCoefficients.{u} l) (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius
    ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m))) F.obj.carrier.X
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Iso.symm_hom] at h1 h2
  ext1
  have e : (F.frobeniusPowUpperStarIso (m + 1)).hom =
      (ProEtale.upperStarIsoLowerStarInv _ _).hom.app F.obj.carrier.X ≫
        (ProEtale.lowerStarCongr _ (congrArg Iso.inv hE)).hom.app F.obj.carrier.X ≫
        (ProEtale.lowerStarComp _ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).inv
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv).inv.app
            F.obj.carrier.X ≫
        (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[_]).map
          ((ProEtale.AdicSheaf.forget _).map (F.frobeniusPowIso m).hom) ≫
        (ProEtale.AdicSheaf.forget _).map F.obj.str.hom := rfl
  rw [e, reassoc_of% h1, reassoc_of% h2]
  simp only [frobeniusPowUpperStarIso, frobeniusUpperStarIso, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [← NatTrans.naturality_assoc]
  rfl

variable {X' : Scheme.{u}} [X'.Over (Spec (CommRingCat.of k₀))]

/-- The Weil structure of the pullback of a pro-étale Weil sheaf. -/
lemma _root_.AlgebraicGeometry.ProEtaleWeilSheaf.upperStar_obj_str (φ : X' ⟶ X)
    [φ.IsOver (Spec (CommRingCat.of k₀))] (K : ProEtaleWeilSheaf k₀ l X) :
    ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj K).str =
      (ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso l φ
          (comp_over φ (Spec (CommRingCat.of k₀)))).app K.carrier ≪≫
        (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))^*ᵃ[l].mapIso
          K.str :=
  IsoAlgebra.mapOfNatIso_obj_str _ K

end AlgebraicGeometry.WeilSheaf
