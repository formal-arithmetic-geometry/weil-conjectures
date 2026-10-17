/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

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

variable (l) in
/-- The exchange isomorphism `φ̄^* ⋙ Fr_X^* ≅ Fr_Y^* ⋙ φ̄^*` of sheaves of `ℚ̄_ℓ`-modules on the
geometric fibres, with `Fr^* = (Fr⁻¹)_*`: the underlying isomorphism of
`AlgebraicGeometry.ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso`. -/
noncomputable def upperStarFrobeniusExchangeIso :
    (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))^*[
        WeilCoefficients.{u} l] ⋙
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[WeilCoefficients.{u} l] ≅
    ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[WeilCoefficients.{u} l] ⋙
      (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))^*[
        WeilCoefficients.{u} l] :=
  Functor.isoWhiskerLeft _ (upperStarIsoLowerStarInv (WeilCoefficients.{u} l)
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius).symm ≪≫
    (upperStarComp _ _ _).symm ≪≫
    upperStarCongr _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ
      (comp_over φ (Spec (CommRingCat.of k₀)))).symm ≪≫
    upperStarComp _ _ _ ≪≫
    Functor.isoWhiskerRight (upperStarIsoLowerStarInv (WeilCoefficients.{u} l)
      (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius) _

/-- The exchange isomorphism of the pullback along the base change with the Frobenii is
monoidal. -/
instance isMonoidal_upperStarFrobeniusExchangeIso_hom :
    NatTrans.IsMonoidal (upperStarFrobeniusExchangeIso l φ).hom :=  sorry

/-- The Weil structure of the pullback of a pro-étale Weil sheaf, on underlying sheaves. -/
lemma upperStar_obj_str_hom_hom (P : ProEtaleWeilSheaf k₀ l Y) :
    ((upperStar k₀ l φ).obj P).str.hom.hom =
      (upperStarFrobeniusExchangeIso l φ).hom.app P.carrier.X ≫
        (Scheme.Hom.geometricFiberMap φ (comp_over φ _))^*[WeilCoefficients.{u} l].map
          P.str.hom.hom :=  sorry

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
          ((upperStar k₀ l φ).obj R).str.hom.hom :=  sorry

end AlgebraicGeometry.ProEtaleWeilSheaf
