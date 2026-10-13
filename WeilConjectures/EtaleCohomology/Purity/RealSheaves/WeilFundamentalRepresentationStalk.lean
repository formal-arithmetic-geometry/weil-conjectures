/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentation
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathFrobeniusElement
public import WeilConjectures.WeilSheaf.StalkCharpoly

/-!
# The local Frobenius and the Weil fundamental representation

Let `ℱ` be a lisse Weil sheaf on the curve `C₀`, `x` a closed point of degree `m` with geometric
point `xb`, and `π : F_xb ≅ F_t` a path to the base point. Transporting the stalk `ℱ_xb` with its
local Frobenius `Fₓ` along `π` gives the stalk `ℱ_t` with the operator `Φᵐ ρ_geom(h)`, where
`Φ` is the Frobenius of the Weil fundamental representation and `h` the loop at `t` obtained
from the local Frobenius loop `F_t ≅ F_xb ≅ F_{σᵐ ≫ xb} = F_{xb ≫ Frᵐ} ≅ F_{t ≫ Frᵐ}`
(`AlgebraicGeometry.WeilGroup.BasePointData.frobeniusLoop`) and the iterate `β_m` of the path
`β : F_t ≅ F_{t ≫ Fr}` (`AlgebraicGeometry.WeilGroup.monoLinear_stalk_frobenius`).

The main step is the description of `Φᵐ` through the iterated Weil structure `φ_m`
(`AlgebraicGeometry.WeilGroup.frobPowStalk_frobPathPow`): for a path `δ : F_t ≅ F_{t ≫ Frᵐ}`
let `Ψ_m(δ)` be the transport along `δ` followed by `ℱ_{t ≫ Frᵐ} = ((Frᵐ)^* ℱ)_t` and the stalk
of `φ_m : (Frᵐ)^* ℱ ≅ ℱ`; then `Ψ_m(β_m) = Φᵐ`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilGroup

open ProEtale Scheme.FiniteEtale

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} [C.Over (Spec (.of K))]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)] [IsCurve (C ↘ Spec (.of K))]
  {W : WeilGroup (C ↘ Spec (.of K))}
  (M : LisseMonodromy l (C ↘ Spec (.of K)).geometricFiber (AlgebraicClosure K))
  {B : BasePointData W}

omit [Finite K] [Fact (ringChar K ≠ l)] [IsCurve (C ↘ Spec (.of K))] in
/-- Transport along the path given by an equality of geometric points is the identification of
the stalks. -/
lemma mono_eqToIso_hom_app {y z : Spec (.of (AlgebraicClosure K)) ⟶
    (C ↘ Spec (.of K)).geometricFiber} (h : y = z) (G : LisseSheaf l _) :
    (M.mono (eqToIso (congrArg fiber h))).hom.app G =
      (Sheaf.Γ _ _).map ((upperStarCongr _ h).hom.app G.obj.X) := by
  subst h
  simp [M.mono_refl, upperStarCongr]
  rfl

/-- The iterated Weil structure `φ_m : (Frᵐ)^* ℱ ≅ ℱ` as an isomorphism of lisse sheaves. -/
noncomputable def _root_.AlgebraicGeometry.WeilSheaf.lisseFrobPowStr (F : WeilSheaf K l C)
    (hF : F.IsLisse) (n : ℕ) :
    (F.toLisse hF).upperStar l ((C ↘ Spec (.of K)).geometricGaloisFrobenius ^ n).hom ≅
      F.toLisse hF :=
  (ObjectProperty.fullyFaithfulι _).preimageIso
    ((adicUpperStarIsoLowerStarInv l ((C ↘ Spec (.of K)).geometricGaloisFrobenius ^ n)).app _ ≪≫
      F.frobeniusPowIso n)

omit [IsCurve (C ↘ Spec (.of K))] in
lemma _root_.AlgebraicGeometry.WeilSheaf.lisseFrobPowStr_hom_hom (F : WeilSheaf K l C)
    (hF : F.IsLisse) (n : ℕ) :
    (F.lisseFrobPowStr hF n).hom.hom.hom = F.frobeniusPowStr n := by
  change ((adicUpperStarIsoLowerStarInv l _).hom.app _ ≫ (F.frobeniusPowIso n).hom).hom = _
  rw [Mod.comp_hom', adicUpperStarIsoLowerStarInv_hom_app_hom]
  rfl

omit [IsCurve (C ↘ Spec (.of K))] in
lemma _root_.AlgebraicGeometry.WeilSheaf.lisseFrobStr_hom_hom_hom' (F : WeilSheaf K l C)
    (hF : F.IsLisse) : (F.lisseFrobStr hF).hom.hom.hom = F.frobeniusStr := by
  change ((adicUpperStarIsoLowerStarInv l _).hom.app _ ≫ F.obj.str.hom).hom = _
  rw [Mod.comp_hom', adicUpperStarIsoLowerStarInv_hom_app_hom]
  rfl

variable (B) in
/-- The operator `Ψ_n(δ)` on the stalk `ℱ_t`, for a path `δ : F_t ≅ F_{t ≫ Frⁿ}`: transport along
`δ`, the identification `ℱ_{t ≫ Frⁿ} = ((Frⁿ)^* ℱ)_t`, and the stalk of the iterated Weil
structure `φ_n`. -/
noncomputable def frobPowStalk (F : WeilSheaf K l C) (hF : F.IsLisse) (n : ℕ)
    (δ : fiber B.t ≅ fiber (B.t ≫ ((C ↘ Spec (.of K)).geometricGaloisFrobenius ^ n).hom)) :
    (lisseStalk l B.t).obj (F.toLisse hF) ⟶ (lisseStalk l B.t).obj (F.toLisse hF) :=
  (M.mono δ).hom.app _ ≫
    (upperStarStalkIso l ((C ↘ Spec (.of K)).geometricGaloisFrobenius ^ n).hom B.t
      F.obj.carrier.X).hom ≫
    (lisseStalk l B.t).map (F.lisseFrobPowStr hF n).hom

omit [Finite K] [Fact (ringChar K ≠ l)] [IsCurve (C ↘ Spec (.of K))] in
/-- Associativity of the identifications `Γ(Spec, (t ≫ f ≫ g)^* G) ≅ Γ(Spec, t^* f^* g^* G)`. -/
lemma Γ_map_upperStarComp_comp {S P Z Y : Scheme.{u}} (t : S ⟶ P) (f : P ⟶ Z) (g : Z ⟶ Y)
    {h : P ⟶ Y} (e : f ≫ g = h) (G : Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l)) :
    (Sheaf.Γ _ _).map ((upperStarComp _ (t ≫ f) g).hom.app G) ≫
        (Sheaf.Γ _ _).map ((upperStarComp _ t f).hom.app ((g)^*[_].obj G)) =
      (Sheaf.Γ _ _).map ((upperStarCongr (WeilCoefficients.{u} l)
          (show (t ≫ f) ≫ g = t ≫ h by rw [Category.assoc, e])).hom.app G) ≫
        (Sheaf.Γ _ _).map ((upperStarComp _ t h).hom.app G) ≫
        (Sheaf.Γ _ _).map ((t)^*[_].map ((upperStarFactor _ e).hom.app G)) := by
  subst e
  rw [upperStarFactor_rfl, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
    upperStarComp_hom_app_comp_upperStarComp_hom_app]

/-- Changing the path in `Ψ_n` multiplies by the monodromy of a loop. -/
lemma frobPowStalk_eq_mono_comp (F : WeilSheaf K l C) (hF : F.IsLisse) (n : ℕ)
    (δ δ' : fiber B.t ≅ fiber (B.t ≫ ((C ↘ Spec (.of K)).geometricGaloisFrobenius ^ n).hom)) :
    frobPowStalk M B F hF n δ =
      (M.mono (δ ≪≫ δ'.symm)).hom.app _ ≫ frobPowStalk M B F hF n δ' := by
  have : δ = (δ ≪≫ δ'.symm) ≪≫ δ' := by simp
  conv_lhs => rw [this]
  simp only [frobPowStalk, M.mono_trans, Iso.trans_hom, NatTrans.comp_app, Category.assoc]

/-- `Ψ_m(δ)` followed by the Frobenius `Φ` is `Ψ_{m+1}(δ ≫ (Frᵐ)_* β)`: this is
`φ_{m+1} = φ ∘ Fr^* φ_m` on the stalks. -/
theorem frobPowStalk_comp_frobStalkIso (F : WeilSheaf K l C) (hF : F.IsLisse) (m : ℕ)
    (δ : fiber B.t ≅ fiber (B.t ≫ ((C ↘ Spec (.of K)).geometricGaloisFrobenius ^ m).hom)) :
    frobPowStalk M B F hF m δ ≫ (frobStalkIso M B F hF).hom =
      frobPowStalk M B F hF (m + 1) (δ ≪≫
        pullbackPathIso ((C ↘ Spec (.of K)).geometricGaloisFrobenius ^ m).hom B.frobPath ≪≫
        eqToIso (by rw [pow_succ, Aut.Aut_mul_def, Iso.trans_hom, Category.assoc])) := by
  set Fr := (C ↘ Spec (.of K)).geometricGaloisFrobenius
  have e : Fr.hom ≫ (Fr ^ m).hom = (Fr ^ (m + 1)).hom := by
    rw [pow_succ, Aut.Aut_mul_def, Iso.trans_hom]
  -- naturality of the transport along `β` with respect to `φ_m`
  have n₁ : (lisseStalk l B.t).map (F.lisseFrobPowStr hF m).hom ≫
      (M.mono B.frobPath).hom.app (F.toLisse hF) =
      (M.mono B.frobPath).hom.app _ ≫ (lisseStalk l _).map (F.lisseFrobPowStr hF m).hom :=
    (M.mono B.frobPath).hom.naturality _
  -- naturality of `ℱ_{t ≫ Fr} = (Fr^* ℱ)_t` with respect to `φ_m`
  have n₂ := upperStarStalkIso_hom_naturality l Fr.hom B.t (F.lisseFrobPowStr hF m).hom.hom.hom
  -- compatibility of the transport with pullback along `Frᵐ`
  have n₃ := M.mono_upperStar (Fr ^ m).hom B.frobPath (F.toLisse hF)
  -- `φ_{m+1} = φ ∘ Fr^* φ_m`
  have n₄ := F.upperStarFactor_hom_app_comp_frobeniusPowStr_succ m e
  have hE := mono_eqToIso_hom_app M (show (B.t ≫ Fr.hom) ≫ (Fr ^ m).hom =
    B.t ≫ (Fr ^ (m + 1)).hom by rw [Category.assoc, e]) (F.toLisse hF)
  have hC := Γ_map_upperStarComp_comp (l := l) B.t Fr.hom (Fr ^ m).hom e F.obj.carrier.X
  simp only [frobPowStalk, frobStalkIso, M.mono_trans, Iso.trans_hom, NatTrans.comp_app,
    Iso.app_hom, Functor.mapIso_hom, Category.assoc]
  congr 1
  erw [reassoc_of% n₁, ← reassoc_of% n₃]
  congr 1
  erw [reassoc_of% n₂, hE]
  have h₁ : (lisseStalk l B.t).map (F.lisseFrobStr hF).hom =
      (Sheaf.Γ _ _).map ((B.t)^*[_].map F.frobeniusStr) := by
    change (Sheaf.Γ _ _).map ((B.t)^*[_].map (F.lisseFrobStr hF).hom.hom.hom) = _
    rw [WeilSheaf.lisseFrobStr_hom_hom_hom']
  have h₂ : (lisseStalk l B.t).map (F.lisseFrobPowStr hF (m + 1)).hom =
      (Sheaf.Γ _ _).map ((B.t)^*[_].map (F.frobeniusPowStr (m + 1))) := by
    change (Sheaf.Γ _ _).map ((B.t)^*[_].map (F.lisseFrobPowStr hF (m + 1)).hom.hom.hom) = _
    rw [WeilSheaf.lisseFrobPowStr_hom_hom]
  rw [h₁, h₂, ← n₄]
  simp only [upperStarStalkIso, Functor.mapIso_hom, Iso.app_hom, Functor.map_comp,
    Category.assoc]
  rw [WeilSheaf.lisseFrobPowStr_hom_hom]
  erw [reassoc_of% hC]

omit [Finite K] [Fact (ringChar K ≠ l)] [IsCurve (C ↘ Spec (.of K))] in
/-- The identifications `(t ≫ g)^* ≅ t^* g^*` and `g^* ≅ 𝟭` for `g = 𝟙` compose to the
identity. -/
lemma upperStar_id_coherence {S P : Scheme.{u}} (t : S ⟶ P) {g : P ⟶ P} (p : g = 𝟙 P)
    (h : t = t ≫ g) (X : Sheaf (Scheme.ProEt.topology P) (WeilCoefficients.{u} l)) :
    (upperStarCongr _ h).hom.app X ≫ (upperStarComp _ t g).hom.app X ≫
        (t)^*[_].map ((upperStarCongr _ p).hom.app X ≫ (upperStarId _ P).hom.app X) = 𝟙 _ := by
  subst p
  simp [upperStarComp_id_right, upperStarCongr]

/-- `Ψ_0(β_0)` is the identity: `φ_0` is the identification `(𝟙)^* ≅ 𝟭`. -/
theorem frobPowStalk_zero (F : WeilSheaf K l C) (hF : F.IsLisse) :
    frobPowStalk M B F hF 0 (B.frobPathPow 0) = 𝟙 _ := by
  set Fr := (C ↘ Spec (.of K)).geometricGaloisFrobenius
  have p : (Fr ^ 0).hom = 𝟙 _ := by rw [pow_zero]; rfl
  have h : B.t = B.t ≫ (Fr ^ 0).hom := by rw [p, Category.comp_id]
  have h₀ : B.frobPathPow 0 = eqToIso (congrArg fiber h) := rfl
  have h₂ : (lisseStalk l B.t).map (F.lisseFrobPowStr hF 0).hom =
      (Sheaf.Γ _ _).map ((B.t)^*[_].map (F.frobeniusPowStr 0)) := by
    change (Sheaf.Γ _ _).map ((B.t)^*[_].map (F.lisseFrobPowStr hF 0).hom.hom.hom) = _
    rw [WeilSheaf.lisseFrobPowStr_hom_hom]
  simp only [frobPowStalk, h₀, h₂, F.frobeniusPowStr_zero p, upperStarStalkIso,
    Functor.mapIso_hom, Iso.app_hom, Functor.map_comp]
  rw [mono_eqToIso_hom_app M h]
  simp only [← Functor.map_comp, Category.assoc]
  erw [upperStar_id_coherence (l := l) B.t p h]
  exact CategoryTheory.Functor.map_id _ _

/-- **`Ψ_m(β_m) = Φᵐ`**: the transport along the iterated path `β_m` followed by the iterated
Weil structure `φ_m` is the `m`-th power of the Frobenius `Φ` of the Weil fundamental
representation. -/
theorem frobPowStalk_frobPathPow (F : WeilSheaf K l C) (hF : F.IsLisse) (m : ℕ) :
    ((WeilCoefficients.toModuleCat l).map (frobPowStalk M B F hF m (B.frobPathPow m))).hom =
      ((frobStalk M B F hF) ^ m).toLinearMap := by
  induction m with
  | zero =>
    rw [frobPowStalk_zero, CategoryTheory.Functor.map_id, pow_zero]
    rfl
  | succ m ih =>
    have h := frobPowStalk_comp_frobStalkIso M F hF m (B.frobPathPow m)
    rw [show B.frobPathPow (m + 1) = B.frobPathPow m ≪≫ pullbackPathIso
      ((C ↘ Spec (.of K)).geometricGaloisFrobenius ^ m).hom B.frobPath ≪≫ eqToIso (by
        rw [pow_succ, Aut.Aut_mul_def, Iso.trans_hom, Category.assoc]) from rfl, ← h,
      CategoryTheory.Functor.map_comp, ModuleCat.hom_comp, ih, pow_succ']
    rfl

omit [Finite K] [Fact (ringChar K ≠ l)] [IsCurve (C ↘ Spec (.of K))] in
/-- Transport along the inverse path is the inverse transport. -/
lemma mono_symm {y z : Spec (.of (AlgebraicClosure K)) ⟶ (C ↘ Spec (.of K)).geometricFiber}
    (τ : fiber y ≅ fiber z) : M.mono τ.symm = (M.mono τ).symm := by
  have h := M.mono_trans τ τ.symm
  rw [Iso.self_symm_id, M.mono_refl] at h
  ext1
  exact (Iso.inv_ext (congrArg Iso.hom h).symm).symm

omit [Finite K] [Fact (ringChar K ≠ l)] [IsCurve (C ↘ Spec (.of K))] in
/-- The identification of stalks along an equality of geometric points is `eqToHom`. -/
lemma Γ_map_upperStarCongr_hom_app {y z : Spec (.of (AlgebraicClosure K)) ⟶
    (C ↘ Spec (.of K)).geometricFiber} (h : y = z)
    (G : Sheaf (Scheme.ProEt.topology (C ↘ Spec (.of K)).geometricFiber)
      (WeilCoefficients.{u} l)) :
    (Sheaf.Γ _ _).map ((upperStarCongr _ h).hom.app G) =
      eqToHom (congrArg (fun y ↦ (stalkFunctor l y).obj G) h) := by
  subst h
  simp [upperStarCongr]

/-- Transport along a path `π : F_xb ≅ F_t` intertwines the local Frobenius at a closed point
`x` of degree `m` with `Ψ_m` of the local Frobenius loop. -/
theorem mono_comp_frobPowStalk_frobeniusLoop (F : WeilSheaf K l C) (hF : F.IsLisse)
    (x : C.finitePoints)
    (π : fiber ((C ↘ Spec (.of K)).geometricFiberPointOfFinitePoint x) ≅ fiber B.t) :
    ((F.stalkObjSpecFrobeniusPowIso _ _).symm ≪≫ eqToIso (congrArg F.stalkObj
        ((C ↘ Spec (.of K)).geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
          x).symm) ≪≫ F.stalkObjFrobeniusPowIso _ _).hom ≫ (M.mono π).hom.app (F.toLisse hF) =
      (M.mono π).hom.app (F.toLisse hF) ≫
        frobPowStalk M B F hF _ (B.frobeniusLoop x π) := by
  have hx := (C ↘ Spec (.of K)).geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow x
  let xb := (C ↘ Spec (.of K)).geometricFiberPointOfFinitePoint x
  let m := (C ↘ Spec (.of K)).degreeOver x.1
  let Fr := (C ↘ Spec (.of K)).geometricGaloisFrobenius
  let R := fiberReparamIso (specGeometricFrobenius K ^ m) xb
  have hloop : π ≪≫ B.frobeniusLoop x π = R.symm ≪≫ eqToIso (congrArg fiber hx.symm) ≪≫
      pullbackPathIso (Fr ^ m).hom π := by
    rw [BasePointData.frobeniusLoop, Iso.self_symm_id_assoc]
  have e₁ := M.mono_upperStar (Fr ^ m).hom π (F.toLisse hF)
  have e₂ : (M.mono π).hom.app _ ≫ (lisseStalk l B.t).map (F.lisseFrobPowStr hF m).hom =
      (lisseStalk l xb).map (F.lisseFrobPowStr hF m).hom ≫ (M.mono π).hom.app _ :=
    ((M.mono π).hom.naturality _).symm
  have e₃ := M.mono_reparam (specGeometricFrobenius K ^ m) xb (F.toLisse hF)
  have e₄ := mono_eqToIso_hom_app M hx.symm (F.toLisse hF)
  have e₅ : (lisseStalk l xb).map (F.lisseFrobPowStr hF m).hom =
      (Sheaf.Γ _ _).map ((xb)^*[_].map (F.frobeniusPowStr m)) := by
    change (Sheaf.Γ _ _).map ((xb)^*[_].map (F.lisseFrobPowStr hF m).hom.hom.hom) = _
    rw [WeilSheaf.lisseFrobPowStr_hom_hom]
  have key : (M.mono π).hom.app (F.toLisse hF) ≫ frobPowStalk M B F hF _ (B.frobeniusLoop x π) =
      (M.mono R.symm).hom.app (F.toLisse hF) ≫
        (M.mono (eqToIso (congrArg fiber hx.symm))).hom.app (F.toLisse hF) ≫
        (upperStarStalkIso l (Fr ^ m).hom xb F.obj.carrier.X).hom ≫
        (lisseStalk l xb).map (F.lisseFrobPowStr hF m).hom ≫ (M.mono π).hom.app (F.toLisse hF) := by
    have h₀ := congrArg (fun τ ↦ (M.mono τ).hom.app (F.toLisse hF)) hloop
    simp only [M.mono_trans, Iso.trans_hom, NatTrans.comp_app] at h₀
    simp only [frobPowStalk, ← Category.assoc]
    rw [h₀]
    simp only [Category.assoc]
    rw [reassoc_of% e₁, e₂]
  have hmain : ((F.stalkObjSpecFrobeniusPowIso _ _).symm ≪≫ eqToIso (congrArg F.stalkObj hx.symm) ≪≫
      F.stalkObjFrobeniusPowIso _ _).hom =
      (M.mono R.symm).hom.app (F.toLisse hF) ≫
        (M.mono (eqToIso (congrArg fiber hx.symm))).hom.app (F.toLisse hF) ≫
        (upperStarStalkIso l (Fr ^ m).hom xb F.obj.carrier.X).hom ≫
        (lisseStalk l xb).map (F.lisseFrobPowStr hF m).hom := by
    have e₃' : (M.mono R).app (F.toLisse hF) = F.stalkObjSpecFrobeniusPowIso m xb := Iso.ext e₃
    rw [mono_symm, Iso.symm_hom, ← Iso.app_inv, e₃', e₄, Γ_map_upperStarCongr_hom_app, e₅]
    simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, WeilSheaf.stalkObjFrobeniusPowIso,
      upperStarStalkIso, Functor.mapIso_hom, Iso.app_hom, Functor.map_comp, Category.assoc,
      WeilSheaf.frobeniusPowStr]
    rfl
  rw [key, hmain]
  simp only [Category.assoc]

end AlgebraicGeometry.WeilGroup
