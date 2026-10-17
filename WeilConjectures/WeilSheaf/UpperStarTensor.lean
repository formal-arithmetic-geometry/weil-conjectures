/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseInternalHom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.MonoidalIso
public import WeilConjectures.WeilSheaf.TensorHomAdjunction
public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction

/-!
# Pullbacks of pro-étale Weil sheaves and tensor products

Let `φ : X ⟶ Y` be a morphism of `k₀`-schemes. The pullback `φ^*` of pro-étale Weil sheaves is
compatible with tensor products: the isomorphism `φ^*(P ⊗ M) ≅ φ^* P ⊗ φ^* M` of the underlying
sheaves of `ℚ̄_ℓ,X̄`-modules intertwines the Weil structures
(`AlgebraicGeometry.ProEtaleWeilSheaf.tensorFunctorCompUpperStarIso`).

The Weil structure `Fr_X^* φ^* P ≅ φ^* P` of a pullback is transported from that of `P` along
`Fr_X^* φ̄^* ≅ (φ̄ ≫ Fr_Y)^* ≅ φ̄^* Fr_Y^*`, a composite of monoidal isomorphisms of pullback functors
(`AlgebraicGeometry.ProEtaleWeilSheaf.frobeniusStr_upperStar`). Hence the pullback of a pairing
compatible with the Weil structures is again compatible with the Weil structures
(`AlgebraicGeometry.ProEtaleWeilSheaf.upperStar_pairing_str`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal

namespace AlgebraicGeometry

open ProEtale Endofunctor

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]

namespace ProEtaleWeilSheaf

section FrobeniusStr

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

set_option hygiene false in
local notation "Fr" =>
  ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[WeilCoefficients.{u} l]

set_option hygiene false in
local notation "Fr'" =>
  ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[WeilCoefficients.{u} l]

set_option hygiene false in
local notation "ι" => upperStarIsoLowerStarInv (WeilCoefficients.{u} l)
  (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius

/-- The Weil structure `Fr^* P ⟶ P` of a pro-étale Weil sheaf on the underlying sheaf of
`ℚ̄_ℓ`-modules, with `Fr^*` the pullback along the geometric Frobenius. -/
noncomputable def frobeniusStr (P : ProEtaleWeilSheaf k₀ l X) : (Fr').obj P.carrier.X ⟶ P.carrier.X :=
  (ι).hom.app P.carrier.X ≫ P.str.hom.hom

/-- A pairing is compatible with the Weil structures in the pushforward form `Fr^* = (Fr⁻¹)_*` if
and only if it is in the pullback form. -/
lemma pairing_str_iff (P Q R : ProEtaleWeilSheaf k₀ l X)
    (e : P.carrier.X ⊗ Q.carrier.X ⟶ R.carrier.X) :
    (P.str.hom.hom ⊗ₘ Q.str.hom.hom) ≫ e = μ Fr _ _ ≫ (Fr).map e ≫ R.str.hom.hom ↔
      (frobeniusStr P ⊗ₘ frobeniusStr Q) ≫ e = μ Fr' _ _ ≫ (Fr').map e ≫ frobeniusStr R := by
  have hμ := NatTrans.IsMonoidal.tensor (τ := (ι).hom) P.carrier.X Q.carrier.X
  have hn := (ι).hom.naturality e
  rw [frobeniusStr, frobeniusStr, frobeniusStr, ← tensorHom_comp_tensorHom_assoc]
  constructor
  · intro h
    rw [h, ← reassoc_of% hμ, ← reassoc_of% hn]
  · intro h
    rw [← cancel_epi ((ι).hom.app P.carrier.X ⊗ₘ (ι).hom.app Q.carrier.X), h, ← reassoc_of% hμ,
      ← reassoc_of% hn]

end FrobeniusStr

section UpperStar

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]

set_option hygiene false in
local notation "φ̄" => Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀)))

set_option hygiene false in
local notation "σX" => (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius

set_option hygiene false in
local notation "σY" => (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius

/-- The Weil structure of `φ^* P` is transported from that of `P`. -/
lemma upperStar_obj_str (P : ProEtaleWeilSheaf k₀ l Y) :
    ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj P).str =
      (adicUpperStarGeometricFiberMapCompFrobeniusIso l φ
          (comp_over φ (Spec (CommRingCat.of k₀)))).app P.carrier ≪≫
        (φ̄)^*ᵃ[l].mapIso P.str :=
  IsoAlgebra.mapOfNatIso_obj_str _ P

private lemma frobeniusStr_upperStar_aux (P : ProEtaleWeilSheaf k₀ l Y) :
    frobeniusStr ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj P) =
      (upperStarIsoLowerStarInv (WeilCoefficients.{u} l) σX).hom.app
          ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj P).carrier.X ≫
      (upperStarIsoLowerStarInv (WeilCoefficients.{u} l) σX).inv.app
          ((φ̄)^*ᵃ[l].obj P.carrier).X ≫
      (upperStarComp _ (σX).hom φ̄).inv.app P.carrier.X ≫
        (upperStarCongr _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
          φ (comp_over φ (Spec (CommRingCat.of k₀)))).symm).hom.app P.carrier.X ≫
        (upperStarComp _ φ̄ (σY).hom).hom.app P.carrier.X ≫
        (φ̄)^*[_].map (frobeniusStr P) := by
  rw [frobeniusStr, upperStar_obj_str, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  change _ ≫ ((adicUpperStarGeometricFiberMapCompFrobeniusIso l φ
    (comp_over φ (Spec (CommRingCat.of k₀)))).hom.app P.carrier ≫ _).hom = _
  rw [Mod.comp_hom', adicUpperStar_map_hom,
    adicUpperStarGeometricFiberMapCompFrobeniusIso_hom_app_hom, frobeniusStr, Functor.map_comp]
  simp only [Category.assoc]

private lemma hom_inv_id_app_upperStar_assoc
    {F G : Sheaf (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (WeilCoefficients.{u} l) ⥤
        Sheaf (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
          (WeilCoefficients.{u} l)} (α : F ≅ G) (P : ProEtaleWeilSheaf k₀ l Y) {Z}
    (h : F.obj ((φ̄)^*ᵃ[l].obj P.carrier).X ⟶ Z) :
    α.hom.app ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj P).carrier.X ≫
      α.inv.app ((φ̄)^*ᵃ[l].obj P.carrier).X ≫ h = h :=
  Iso.hom_inv_id_app_assoc α _ h

/-- The Weil structure of the pullback `φ^* P`, in pullback form: the pullback along `φ̄` of that
of `P`, through `Fr_X^* φ̄^* ≅ (Fr_X ≫ φ̄)^* = (φ̄ ≫ Fr_Y)^* ≅ φ̄^* Fr_Y^*`. -/
lemma frobeniusStr_upperStar (P : ProEtaleWeilSheaf k₀ l Y) :
    frobeniusStr ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj P) =
      (upperStarComp _ (σX).hom φ̄).inv.app P.carrier.X ≫
        (upperStarCongr _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
          φ (comp_over φ (Spec (CommRingCat.of k₀)))).symm).hom.app P.carrier.X ≫
        (upperStarComp _ φ̄ (σY).hom).hom.app P.carrier.X ≫
        (φ̄)^*[_].map (frobeniusStr P) :=
  (frobeniusStr_upperStar_aux φ P).trans (hom_inv_id_app_upperStar_assoc φ _ _ _)

/-- **Pullbacks of compatible pairings are compatible**, in pullback form. -/
theorem upperStar_pairing_frobeniusStr (P Q R : ProEtaleWeilSheaf k₀ l Y)
    (e : P.carrier.X ⊗ Q.carrier.X ⟶ R.carrier.X)
    (h : (frobeniusStr P ⊗ₘ frobeniusStr Q) ≫ e =
      μ ((σY).hom)^*[WeilCoefficients.{u} l] _ _ ≫ ((σY).hom)^*[_].map e ≫ frobeniusStr R) :
    (frobeniusStr ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj P) ⊗ₘ
        frobeniusStr ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj Q)) ≫
        (μ (φ̄)^*[WeilCoefficients.{u} l] P.carrier.X Q.carrier.X ≫ (φ̄)^*[_].map e) =
      μ ((σX).hom)^*[WeilCoefficients.{u} l] _ _ ≫
        ((σX).hom)^*[_].map (μ (φ̄)^*[WeilCoefficients.{u} l] P.carrier.X Q.carrier.X ≫
          (φ̄)^*[_].map e) ≫ frobeniusStr ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj R) := by
  set ψ := (upperStarComp (WeilCoefficients.{u} l) (σX).hom φ̄).symm ≪≫
    upperStarCongr _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
      φ (comp_over φ (Spec (CommRingCat.of k₀)))).symm ≪≫
    upperStarComp _ φ̄ (σY).hom
  have hψ : NatTrans.IsMonoidal ψ.hom := by
    simp only [ψ, Iso.trans_hom, Iso.symm_hom]
    infer_instance
  have hψt := NatTrans.IsMonoidal.tensor (τ := ψ.hom) P.carrier.X Q.carrier.X
  have nψ := ψ.hom.naturality e
  have hs (S : ProEtaleWeilSheaf k₀ l Y) : frobeniusStr ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj S) =
      ψ.hom.app S.carrier.X ≫ (φ̄)^*[_].map (frobeniusStr S) := by
    rw [frobeniusStr_upperStar]
    simp [ψ]
  simp only [Functor.LaxMonoidal.comp_μ, Functor.comp_map, Functor.comp_obj] at hψt nψ
  rw [hs, hs, hs, ← tensorHom_comp_tensorHom_assoc, μ_natural_assoc, ← Functor.map_comp, h]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hψt, reassoc_of% nψ]

end UpperStar

section Tensor

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]

set_option hygiene false in
local notation "φ̄" => Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀)))

set_option hygiene false in
local notation "FrX" =>
  ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[WeilCoefficients.{u} l]

attribute [local instance] Sheaf.symmetricCategory

/-- **Pullbacks of compatible pairings are compatible**, in pushforward form. -/
theorem upperStar_pairing_str (P Q R : ProEtaleWeilSheaf k₀ l Y)
    (e : P.carrier.X ⊗ Q.carrier.X ⟶ R.carrier.X)
    (h : (P.str.hom.hom ⊗ₘ Q.str.hom.hom) ≫ e =
      μ ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[WeilCoefficients.{u} l]
        _ _ ≫ ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[_].map e ≫
        R.str.hom.hom) :
    (((ProEtaleWeilSheaf.upperStar k₀ l φ).obj P).str.hom.hom ⊗ₘ
        ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj Q).str.hom.hom) ≫
        (μ (φ̄)^*[WeilCoefficients.{u} l] P.carrier.X Q.carrier.X ≫ (φ̄)^*[_].map e) =
      μ FrX _ _ ≫ (FrX).map (μ (φ̄)^*[WeilCoefficients.{u} l] P.carrier.X Q.carrier.X ≫
          (φ̄)^*[_].map e) ≫ ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj R).str.hom.hom :=
  (pairing_str_iff ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj P)
    ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj Q) ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj R)
    _).2 (upperStar_pairing_frobeniusStr φ P Q R e ((pairing_str_iff P Q R e).1 h))

/-- The isomorphism `φ^*(P ⊗ M) ≅ φ^* P ⊗ φ^* M` is compatible with the Weil structures. -/
lemma upperStarTensorLeftIso_str (M P : ProEtaleWeilSheaf k₀ l Y) :
    (WeilSheaf.frobeniusPullback k₀ l X).map
        ((adicUpperStarTensorLeftIso l φ̄ M.carrier).hom.app P.carrier) ≫
        (ProEtaleWeilSheaf.tensor k₀ l X ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj M)
          ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj P)).str.hom =
      ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj
        ((ProEtaleWeilSheaf.tensorFunctor k₀ l Y M).obj P)).str.hom ≫
        (adicUpperStarTensorLeftIso l φ̄ M.carrier).hom.app P.carrier := by
  set T := (adicUpperStarTensorLeftIso l φ̄ M.carrier).app P.carrier
  have : PreservesColimitsOfShape WalkingParallelPair
      (Mod.mapModComap (G := (φ̄)^*[WeilCoefficients.{u} l]) (adicUpperStarRingHom l φ̄)) :=
    inferInstanceAs (PreservesColimitsOfShape WalkingParallelPair (φ̄)^*ᵃ[l])
  have h₁ := Mod.map_tensorπ_comp_tensorLeftCompMapModComapIso_hom (adicUpperStarRingHom l φ̄)
    (fun _ _ ↦ Adjunction.μ_comp_map_braiding (ProEtale.upperStarLowerStarAdjunction _ φ̄) _ _)
    P.carrier M.carrier
  have hT : Mod.tensorπ ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj P).carrier
      ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj M).carrier ≫ T.inv.hom =
      μ (φ̄)^*[WeilCoefficients.{u} l] P.carrier.X M.carrier.X ≫
        (φ̄)^*[_].map (Mod.tensorπ P.carrier M.carrier) := by
    rw [← cancel_mono T.hom.hom, Category.assoc, ← Mod.comp_hom', T.inv_hom_id]
    erw [Mod.id_hom', Category.comp_id]
    rw [Category.assoc]
    erw [h₁]
    simp only [IsIso.hom_inv_id_assoc]
    rfl
  rw [← cancel_epi ((WeilSheaf.frobeniusPullback k₀ l X).map T.inv), ← Functor.map_comp_assoc]
  simp only [T, Iso.app_inv, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  refine frobeniusPullback_tensor_hom_ext (P := (ProEtaleWeilSheaf.upperStar k₀ l φ).obj P)
    (M := (ProEtaleWeilSheaf.upperStar k₀ l φ).obj M) ?_
  have hp := upperStar_pairing_str φ P M ((ProEtaleWeilSheaf.tensorFunctor k₀ l Y M).obj P)
    (Mod.tensorπ P.carrier M.carrier) (tensorπ_str P M)
  rw [Mod.comp_hom', Mod.comp_hom']
  refine (tensorπ_str _ _).symm.trans ?_
  erw [adicLowerStar_map_hom]
  rw [← (FrX).map_comp_assoc]
  erw [hT]
  refine Eq.trans ?_ ((reassoc_of% hp) _)
  refine congrArg (_ ≫ ·) (Eq.trans ?_ ((reassoc_of% hT) _))
  erw [← Mod.comp_hom', T.inv_hom_id, Mod.id_hom', Category.comp_id]

/-- The component of `tensorFunctorCompUpperStarIso`. -/
noncomputable def tensorFunctorCompUpperStarIsoApp (M P : ProEtaleWeilSheaf k₀ l Y) :
    (ProEtaleWeilSheaf.tensorFunctor k₀ l Y M ⋙ ProEtaleWeilSheaf.upperStar k₀ l φ).obj P ≅
      (ProEtaleWeilSheaf.upperStar k₀ l φ ⋙ ProEtaleWeilSheaf.tensorFunctor k₀ l X
          ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj M)).obj P :=
  ObjectProperty.isoMk _
    (Algebra.isoMk ((adicUpperStarTensorLeftIso l φ̄ M.carrier).app P.carrier)
      (upperStarTensorLeftIso_str φ M P))

lemma tensorFunctorCompUpperStarIsoApp_hom_hom_f (M P : ProEtaleWeilSheaf k₀ l Y) :
    (tensorFunctorCompUpperStarIsoApp φ M P).hom.hom.f =
      (adicUpperStarTensorLeftIso l φ̄ M.carrier).hom.app P.carrier :=
  rfl

lemma upperStar_map_hom_f {P Q : ProEtaleWeilSheaf k₀ l Y} (f : P ⟶ Q) :
    ((ProEtaleWeilSheaf.upperStar k₀ l φ).map f).hom.f = (φ̄)^*ᵃ[l].map f.hom.f :=
  rfl

variable (k₀ l) in
/-- **Pullback commutes with tensor products of pro-étale Weil sheaves**:
`φ^*(P ⊗ M) ≅ φ^* P ⊗ φ^* M`, naturally in `P`. -/
noncomputable def tensorFunctorCompUpperStarIso (M : ProEtaleWeilSheaf k₀ l Y) :
    ProEtaleWeilSheaf.tensorFunctor k₀ l Y M ⋙ ProEtaleWeilSheaf.upperStar k₀ l φ ≅
      ProEtaleWeilSheaf.upperStar k₀ l φ ⋙
        ProEtaleWeilSheaf.tensorFunctor k₀ l X ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj M) :=
  NatIso.ofComponents (fun P ↦ tensorFunctorCompUpperStarIsoApp φ M P)
    fun f ↦ ObjectProperty.hom_ext _ (Algebra.Hom.ext (by
      simp only [IsoAlgebra.comp_hom_f, Functor.comp_map, upperStar_map_hom_f,
        tensorFunctorCompUpperStarIsoApp_hom_hom_f]
      exact (adicUpperStarTensorLeftIso l φ̄ M.carrier).hom.naturality f.hom.f))

variable (k₀ l) in
/-- **The projection formula for the internal hom of pro-étale Weil sheaves**:
`φ_*[φ^* A, N] ≅ [A, φ_* N]`, naturally in `N`. It is the conjugate, under the adjunctions
`φ^* ⊣ φ_*` and `- ⊗ A ⊣ [A, -]`, of the isomorphism `φ^*(P ⊗ A) ≅ φ^* P ⊗ φ^* A`
(`AlgebraicGeometry.ProEtaleWeilSheaf.tensorFunctorCompUpperStarIso`). -/
noncomputable def lowerStarCompIhomFunctorIso (A : ProEtaleWeilSheaf k₀ l Y) :
    ProEtaleWeilSheaf.lowerStar k₀ l φ ⋙ ProEtaleWeilSheaf.ihomFunctor k₀ l Y A ≅
      ProEtaleWeilSheaf.ihomFunctor k₀ l X ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj A) ⋙
        ProEtaleWeilSheaf.lowerStar k₀ l φ :=
  conjugateIsoEquiv
    ((tensorIhomAdjunction k₀ l Y A).comp (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l φ))
    ((ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l φ).comp
      (tensorIhomAdjunction k₀ l X ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj A)))
    (tensorFunctorCompUpperStarIso k₀ l φ A).symm

end Tensor

end ProEtaleWeilSheaf

end AlgebraicGeometry
