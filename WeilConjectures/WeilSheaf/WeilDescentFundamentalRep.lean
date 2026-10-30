/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.WeilDescentFundamentalGroup
public import WeilConjectures.WeilSheaf.WeilDescentPullbackRepresentation

/-!
# Weil fundamental representations of pulled-back sheaves

Let `X₀` be a scheme over the finite field `K`, `π : X ⟶ X₀` the projection of its geometric
fibre and `B = (t, β)` base point data, with Weil group `W = π₁(X, t) ⋊ ℤ`, and monodromies `M₀`
on `X₀` and `M` on `X` compatible with `π`
(`AlgebraicGeometry.ProEtale.LisseMonodromy.IsCompatible`). For a lisse sheaf `H` on `X₀`, the
Weil fundamental representation of the Weil sheaf `π^* H` (with its canonical Weil structure,
`AlgebraicGeometry.WeilSheaf.geometricFiberPullback`) is, under the identification
`H_{t ≫ π} ≅ (π^* H)_t`, the restriction of the monodromy representation of `π₁(X₀, t ≫ π)` on
`H_{t ≫ π}` along `toArith : W → π₁(X₀, t ≫ π)`
(`AlgebraicGeometry.FrobeniusBasePoint.fundamentalRep_geometricFiberPullback`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

open ProEtale Scheme.FiniteEtale Representation

namespace ProEtale.LisseMonodromy

variable {l : ℕ} [Fact l.Prime] {Ω : Type u} [Field Ω] {Y Z : Scheme.{u}}

/-- The identification `H_{(t ≫ φ) ≫ p} = H_{t ≫ p} = (p^* H)_t` along `φ ≫ p = p` is the
identification `H_{(t ≫ φ) ≫ p} = (p^* H)_{t ≫ φ} = (φ^* p^* H)_t` followed by the stalk of
`φ^* p^* H ≅ (φ ≫ p)^* H = p^* H`. -/
lemma upperStarStalkIso_comp_coherence (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Z) (φ : Z ⟶ Z)
    (p : Z ⟶ Y) (hφ : φ ≫ p = p) (h : (t ≫ φ) ≫ p = t ≫ p)
    (N : Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l)) :
    (Sheaf.Γ _ _).map ((upperStarCongr _ h).hom.app N) ≫ (upperStarStalkIso l p t N).hom =
      (upperStarStalkIso l p (t ≫ φ) N).hom ≫ (upperStarStalkIso l φ t ((p)^*[_].obj N)).hom ≫
        (stalkFunctor l t).map ((upperStarComp _ φ p).inv.app N ≫
          (upperStarCongr _ hφ).hom.app N) := by
  simp only [upperStarStalkIso, Functor.mapIso_hom, Iso.app_hom, Functor.comp_map,
    ← Functor.map_comp]
  rw [upperStarComp_frobenius_coherence]

lemma mono_eqToIso_hom_app_comp_upperStarStalkIso (M₀ : LisseMonodromy l Y Ω) {p : Z ⟶ Y}
    (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Z) (φ : Z ⟶ Z) (hφ : φ ≫ p = p)
    (h : (t ≫ φ) ≫ p = t ≫ p) (H : LisseSheaf l Y) :
    (M₀.mono (eqToIso (congrArg fiber h))).hom.app H ≫ (upperStarStalkIso l p t H.obj.X).hom =
      (upperStarStalkIso l p (t ≫ φ) H.obj.X).hom ≫
        (upperStarStalkIso l φ t ((p)^*[_].obj H.obj.X)).hom ≫
        (stalkFunctor l t).map ((upperStarComp _ φ p).inv.app H.obj.X ≫
          (upperStarCongr _ hφ).hom.app H.obj.X) := by
  rw [M₀.mono_eqToIso_hom_app h H]
  simp only [upperStarStalkIso, Functor.mapIso_hom, Iso.app_hom, Functor.comp_map,
    ← Functor.map_comp]
  rw [upperStarComp_frobenius_coherence]

/-- For monodromies compatible with `p`, the transport along the push-down
`p_* β : F_{t ≫ p} ≅ F_{(t ≫ φ) ≫ p} = F_{t ≫ p}` of a path `β : F_t ≅ F_{t ≫ φ}`, where
`φ ≫ p = p`, is the transport along `β` of the pullback followed by the stalk of
`φ^* p^* H ≅ (φ ≫ p)^* H = p^* H`. -/
lemma mono_pullbackPathIso_trans_eqToIso_hom_app {M₀ : LisseMonodromy l Y Ω}
    {M : LisseMonodromy l Z Ω} {p : Z ⟶ Y} (hc : IsCompatible p M₀ M)
    (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Z) (φ : Z ⟶ Z) (hφ : φ ≫ p = p)
    (β : fiber t ≅ fiber (t ≫ φ)) (h : (t ≫ φ) ≫ p = t ≫ p) (H : LisseSheaf l Y) :
    (M₀.mono (pullbackPathIso p β ≪≫ eqToIso (congrArg fiber h))).hom.app H ≫
        (upperStarStalkIso l p t H.obj.X).hom =
      (upperStarStalkIso l p t H.obj.X).hom ≫ (M.mono β).hom.app (H.upperStar l p) ≫
        (upperStarStalkIso l φ t ((p)^*[_].obj H.obj.X)).hom ≫
        (stalkFunctor l t).map ((upperStarComp _ φ p).inv.app H.obj.X ≫
          (upperStarCongr _ hφ).hom.app H.obj.X) := by
  rw [M₀.mono_trans, Iso.trans_hom, NatTrans.comp_app, Category.assoc, ← reassoc_of% (hc β H),
    mono_eqToIso_hom_app_comp_upperStarStalkIso M₀ t φ hφ h H]

end ProEtale.LisseMonodromy



namespace FrobeniusBasePoint

variable {K : Type u} [Field K] [Finite K] {X : Scheme.{u}} [X.Over (Spec (.of K))]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)]
  (B : FrobeniusBasePoint K X) (M₀ : LisseMonodromy l X K)
  (M : LisseMonodromy l (X ↘ Spec (.of K)).geometricFiber K)

/-- On a loop `g` at `t`, the Weil fundamental representation of the Weil group
`π₁(X, t) ⋊ ℤ` is the monodromy of `g`. -/
lemma weilData_fundamentalRep_inl (F : WeilSheaf K l X) (hF : F.IsLisse) (g : Aut (fiber B.t)) :
    B.weilData.fundamentalRep M F hF (SemidirectProduct.inl g) = M.rep B.t (F.toLisse hF) g :=
  B.weilData.fundamentalRep_geomEquiv M F hF g

/-- The underlying pro-étale Weil sheaf of `p^* H`. -/
lemma geometricFiberPullback_obj {H : AdicSheaf l X} (hH : IsAdicLisseSheaf H) :
    (WeilSheaf.geometricFiberPullback (k₀ := K) hH).obj =
      (ProEtaleWeilSheaf.geometricFiberPullback K l X).obj H :=
  rfl

/-- The Weil structure `Fr^* p^* H ≅ p^* H` of a pulled-back sheaf is the canonical
identification `Fr^* p^* H ≅ (Fr ≫ p)^* H = p^* H`. -/
lemma adicFrobStr_geometricFiberPullback_hom {H : AdicSheaf l X} (hH : IsAdicLisseSheaf H) :
    (WeilSheaf.geometricFiberPullback (k₀ := K) hH).adicFrobStr.hom =
      (adicUpperStarComp l (X ↘ Spec (.of K)).geometricGaloisFrobenius.hom
          (X ↘ Spec (.of K)).geometricFiberProj).inv.app H ≫
        (adicUpperStarCongr l (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj
          (X ↘ Spec (.of K)))).hom.app H := by
  have e : (WeilSheaf.geometricFiberPullback (k₀ := K) hH).obj.str =
      (ProEtaleWeilSheaf.geometricFiberPullbackFrobeniusIso K l X).app H :=
    ProEtaleWeilSheaf.geometricFiberPullback_obj_str K l X H
  rw [WeilSheaf.adicFrobStr, Iso.trans_hom, Iso.app_hom, e]
  simp only [ProEtaleWeilSheaf.geometricFiberPullbackFrobeniusIso, Iso.trans_hom, Iso.app_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom]
  exact (adicUpperStarIsoLowerStarInv l _).hom_inv_id_app_assoc _ _

/-- The stalk at `y` of the canonical Weil structure `Fr^* p^* H ≅ (Fr ≫ p)^* H = p^* H` of a
pulled-back sheaf. -/
lemma lisseStalk_map_lisseFrobStr_geometricFiberPullback {H : AdicSheaf l X}
    (hH : IsAdicLisseSheaf H)
    (y : Spec (.of (AlgebraicClosure K)) ⟶ (X ↘ Spec (.of K)).geometricFiber) :
    (lisseStalk l y).map ((WeilSheaf.geometricFiberPullback (k₀ := K) hH).lisseFrobStr
        (WeilSheaf.isLisse_geometricFiberPullback hH)).hom =
      (stalkFunctor l y).map
        ((upperStarComp _ (X ↘ Spec (.of K)).geometricGaloisFrobenius.hom
            (X ↘ Spec (.of K)).geometricFiberProj).inv.app H.X ≫
          (upperStarCongr _ (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj
            (X ↘ Spec (.of K)))).hom.app H.X) := by
  have e := congrArg (fun φ ↦ φ.hom) (adicFrobStr_geometricFiberPullback_hom (K := K) hH)
  simp only [Mod.comp_hom', adicUpperStarComp_inv_app_hom, adicUpperStarCongr_hom_app_hom] at e
  rw [← e]
  rfl

/-- **Frobenius coherence of a pulled-back sheaf**: the transport of the stalk of `H` along the
arithmetic Frobenius `π_* β` is, through `H_{t ≫ π} ≅ (π^* H)_t`, the transport along `β`
followed by the stalk of `Fr^* π^* H ≅ (Fr ≫ π)^* H = π^* H`. -/
lemma mono_arithFrob_hom_app
    (hc : LisseMonodromy.IsCompatible (X ↘ Spec (.of K)).geometricFiberProj M₀ M)
    (H : LisseSheaf l X) :
    (M₀.mono B.arithFrob).hom.app H ≫
        (upperStarStalkIso l (X ↘ Spec (.of K)).geometricFiberProj B.t H.obj.X).hom =
      (upperStarStalkIso l (X ↘ Spec (.of K)).geometricFiberProj B.t H.obj.X).hom ≫
        (M.mono B.frobPath).hom.app (H.upperStar l (X ↘ Spec (.of K)).geometricFiberProj) ≫
        (upperStarStalkIso l (X ↘ Spec (.of K)).geometricGaloisFrobenius.hom B.t
          (((X ↘ Spec (.of K)).geometricFiberProj)^*[_].obj H.obj.X)).hom ≫
        (stalkFunctor l B.t).map
          ((upperStarComp _ (X ↘ Spec (.of K)).geometricGaloisFrobenius.hom
              (X ↘ Spec (.of K)).geometricFiberProj).inv.app H.obj.X ≫
            (upperStarCongr _ (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj
              (X ↘ Spec (.of K)))).hom.app H.obj.X) :=
  LisseMonodromy.mono_pullbackPathIso_trans_eqToIso_hom_app hc B.t _
    (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj _) B.frobPath
    (by rw [Category.assoc, Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj]) H

/-- The Frobenius `Φ` of a pulled-back sheaf `π^* H` is, through `H_{t ≫ π} ≅ (π^* H)_t`, the
transport of the stalk of `H` along the arithmetic Frobenius `π_* β`. -/
lemma mono_arithFrob_hom_app_comp_upperStarStalkIso
    (hc : LisseMonodromy.IsCompatible (X ↘ Spec (.of K)).geometricFiberProj M₀ M)
    (H : LisseSheaf l X) :
    (M₀.mono B.arithFrob).hom.app H ≫
        (upperStarStalkIso l (X ↘ Spec (.of K)).geometricFiberProj B.t H.obj.X).hom =
      (upperStarStalkIso l (X ↘ Spec (.of K)).geometricFiberProj B.t H.obj.X).hom ≫
        (frobStalkIso M B (WeilSheaf.geometricFiberPullback (k₀ := K) H.property)
          (WeilSheaf.isLisse_geometricFiberPullback H.property)).hom := by
  rw [B.mono_arithFrob_hom_app M₀ M hc H, frobStalkIso, Iso.trans_hom, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom, lisseStalk_map_lisseFrobStr_geometricFiberPullback]
  rfl

/-- **The Weil fundamental representation of a pulled-back sheaf.** For monodromies `M₀` on
`X₀` and `M` on its geometric fibre compatible with the projection `π`, and a lisse sheaf `H`
on `X₀`, the identification `H_{t ≫ π} ≅ (π^* H)_t` intertwines the monodromy of `H` along the
image `toArith w ∈ π₁(X₀, t ≫ π)` of `w ∈ W` with the Weil fundamental representation of the
Weil sheaf `π^* H`. On `π₁(X, t)` this is the compatibility of the monodromies; at the lift of
the Frobenius it says that the Frobenius `Φ` of `π^* H`, built from `β` and the canonical Weil
structure `Fr^* π^* H ≅ (Fr ≫ π)^* H = π^* H`, is the monodromy of `H` along `π_* β`. -/
theorem fundamentalRep_geometricFiberPullback
    (hc : LisseMonodromy.IsCompatible (X ↘ Spec (.of K)).geometricFiberProj M₀ M)
    (H : LisseSheaf l X) (w : B.WeilGroup)
    (v : LisseMonodromy.StalkSpace (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj) H) :
    LisseMonodromy.upperStarStalkLinearEquiv (X ↘ Spec (.of K)).geometricFiberProj B.t H
        (M₀.rep (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj) H (B.toArith w) v) =
      B.weilData.fundamentalRep M (WeilSheaf.geometricFiberPullback (k₀ := K) H.property)
        (WeilSheaf.isLisse_geometricFiberPullback H.property) w
        (LisseMonodromy.upperStarStalkLinearEquiv (X ↘ Spec (.of K)).geometricFiberProj B.t H
          v) := by
  refine B.weilData.intertwines_of_geometric_frobLift
    ((M₀.rep (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj) H).comp B.toArith) _
    (LisseMonodromy.upperStarStalkLinearEquiv (X ↘ Spec (.of K)).geometricFiberProj B.t H
      ).toLinearMap (fun u hu v ↦ ?_) (fun v ↦ ?_) w v
  · obtain ⟨g, rfl⟩ := SemidirectProduct.range_inl_eq_ker_rightHom.ge hu
    rw [MonoidHom.comp_apply, toArith_inl, pullbackPathHom_apply, LinearEquiv.coe_coe,
      hc.rep_apply]
    exact (LinearMap.congr_fun (B.weilData_fundamentalRep_inl M
      (WeilSheaf.geometricFiberPullback (k₀ := K) H.property)
      (WeilSheaf.isLisse_geometricFiberPullback H.property) g) _).symm
  · rw [MonoidHom.comp_apply, toArith_frobLift]
    refine Eq.trans ?_ (LinearMap.congr_fun (B.weilData.fundamentalRep_frobLift M
      (WeilSheaf.geometricFiberPullback (k₀ := K) H.property)
      (WeilSheaf.isLisse_geometricFiberPullback H.property)).symm _)
    have h := congrArg (fun φ ↦ ((WeilCoefficients.toModuleCat l).map φ).hom v)
      (B.mono_arithFrob_hom_app_comp_upperStarStalkIso M₀ M hc H)
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h

end FrobeniusBasePoint

end AlgebraicGeometry
