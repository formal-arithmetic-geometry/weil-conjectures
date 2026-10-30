/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.WeilDescentFundamentalGroup
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyIrreducible
public import WeilConjectures.WeilSheaf.GeometricFiberPullbackStr
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

namespace CategoryTheory.Endofunctor.IsoAlgebra

/-- For an algebra `A` equal to `functorOfNatIso P s` at `c`, the structure morphism `A.str`
preceded by a component of a natural transformation `U` is `U_{P c} ≫ s_c`. The equality is a
hypothesis, so that the identity can be instantiated without unfolding `A`. -/
lemma comp_str_hom_heq_of_eq {C : Type*} [Category C] {D : Type*} [Category D] {E E' : C ⥤ C}
    (U : E' ⟶ E) (P : D ⥤ C) (s : P ⋙ E ≅ P) (c : D) (A : IsoAlgebra E)
    (h : A = (functorOfNatIso P s).obj c) :
    HEq (U.app A.carrier ≫ A.str.hom) (U.app (P.obj c) ≫ s.hom.app c) := by
  subst h
  rfl

end CategoryTheory.Endofunctor.IsoAlgebra


namespace AlgebraicGeometry

open ProEtale Scheme.FiniteEtale Representation

namespace ProEtale.LisseMonodromy

variable {l : ℕ} [Fact l.Prime] {Ω : Type u} [Field Ω] {Y Z : Scheme.{u}}

/-- The transport along the path `F_{(t ≫ φ) ≫ p} = F_{t ≫ p}` given by `φ ≫ p = p` is the
identification `H_{(t ≫ φ) ≫ p} = (p^* H)_{t ≫ φ} = (φ^* p^* H)_t` followed by the stalk of
`φ^* p^* H ≅ (φ ≫ p)^* H = p^* H`. -/
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


/-- For monodromies compatible with `p`, the identification `G_{y ≫ p} ≅ (p^* G)_y` intertwines
the transports along a path and along its push-down. -/
lemma IsCompatible.monoLinear_apply {M₀ : LisseMonodromy l Y Ω} {M : LisseMonodromy l Z Ω}
    {p : Z ⟶ Y} (hc : IsCompatible p M₀ M) {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ Z}
    (τ : fiber y ≅ fiber z) (G : LisseSheaf l Y) (v : StalkSpace (y ≫ p) G) :
    upperStarStalkLinearEquiv p z G (M₀.monoLinear (pullbackPathIso p τ) G v) =
      M.monoLinear τ (G.upperStar l p) (upperStarStalkLinearEquiv p y G v) := by
  have h := congrArg (fun φ ↦ ((WeilCoefficients.toModuleCat l).map φ).hom v) (hc τ G)
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

variable (l) in
/-- The canonical Weil structure `φ^* p^* H ≅ (φ ≫ p)^* H = p^* H`, as a morphism of lisse
sheaves. -/
noncomputable def pullbackFrobLisseHom (φ : Z ⟶ Z) {p : Z ⟶ Y} (hφ : φ ≫ p = p)
    (H : LisseSheaf l Y) : (H.upperStar l p).upperStar l φ ⟶ H.upperStar l p :=
  ObjectProperty.homMk ((adicUpperStarComp l φ p).inv.app H.obj ≫
    (adicUpperStarCongr l hφ).hom.app H.obj)

/-- The transport along the path `F_{(t ≫ φ) ≫ p} = F_{t ≫ p}` given by `φ ≫ p = p`, through
the identifications with the stalks of `p^* H`, is the stalk of `φ^* p^* H ≅ p^* H`. -/
lemma upperStarStalkLinearEquiv_monoLinear_eqToIso (M₀ : LisseMonodromy l Y Ω) {p : Z ⟶ Y}
    (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Z) (φ : Z ⟶ Z) (hφ : φ ≫ p = p)
    (h : (t ≫ φ) ≫ p = t ≫ p) (H : LisseSheaf l Y) (w : StalkSpace ((t ≫ φ) ≫ p) H) :
    upperStarStalkLinearEquiv p t H (M₀.monoLinear (eqToIso (congrArg fiber h)) H w) =
      lisseStalkMap t (pullbackFrobLisseHom l φ hφ H)
        (upperStarStalkLinearEquiv φ t (H.upperStar l p)
          (upperStarStalkLinearEquiv p (t ≫ φ) H w)) := by
  have e := congrArg (fun f ↦ ((WeilCoefficients.toModuleCat l).map f).hom w)
    (mono_eqToIso_hom_app_comp_upperStarStalkIso M₀ t φ hφ h H)
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at e
  rw [← adicUpperStarComp_inv_app_hom, ← adicUpperStarCongr_hom_app_hom] at e
  simp only [lisseStalkMap, pullbackFrobLisseHom, Functor.comp_map, ObjectProperty.ι_map,
    ObjectProperty.homMk_hom, Mod.forget_map, Mod.comp_hom', Functor.map_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply]
  exact e

/-- For monodromies compatible with `p`, the transport along the push-down
`p_* β : F_{t ≫ p} ≅ F_{(t ≫ φ) ≫ p} = F_{t ≫ p}` of a path `β : F_t ≅ F_{t ≫ φ}`, where
`φ ≫ p = p`, is the transport along `β` of the pullback followed by the stalk of
`φ^* p^* H ≅ (φ ≫ p)^* H = p^* H`. -/
lemma upperStarStalkLinearEquiv_monoLinear_pullbackPathIso_trans {M₀ : LisseMonodromy l Y Ω}
    {M : LisseMonodromy l Z Ω} {p : Z ⟶ Y} (hc : IsCompatible p M₀ M)
    (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Z) (φ : Z ⟶ Z) (hφ : φ ≫ p = p)
    (β : fiber t ≅ fiber (t ≫ φ)) (h : (t ≫ φ) ≫ p = t ≫ p) (H : LisseSheaf l Y)
    (v : StalkSpace (t ≫ p) H) :
    upperStarStalkLinearEquiv p t H
        (M₀.monoLinear (pullbackPathIso p β ≪≫ eqToIso (congrArg fiber h)) H v) =
      lisseStalkMap t (pullbackFrobLisseHom l φ hφ H)
        (upperStarStalkLinearEquiv φ t (H.upperStar l p)
          (M.monoLinear β (H.upperStar l p) (upperStarStalkLinearEquiv p t H v))) := by
  rw [monoLinear_trans, upperStarStalkLinearEquiv_monoLinear_eqToIso M₀ t φ hφ h H,
    hc.monoLinear_apply]

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

/-- The Frobenius `Φ` of a lisse Weil sheaf is the transport along `β`, followed by the
identification `F_{t ≫ Fr} = (Fr^* F)_t` and the stalk of the Weil structure. -/
lemma frobStalk_apply' (F : WeilSheaf K l X) (hF : F.IsLisse)
    (v : LisseMonodromy.StalkSpace B.t (F.toLisse hF)) :
    frobStalk M B F hF v = lisseStalkMap B.t (F.lisseFrobStr hF).hom
      (LisseMonodromy.upperStarStalkLinearEquiv (X ↘ Spec (.of K)).geometricGaloisFrobenius.hom
        B.t (F.toLisse hF) (M.monoLinear B.frobPath (F.toLisse hF) v)) := by
  rw [frobStalk_apply]
  simp only [frobPathStalkIso, Iso.trans_hom, Iso.app_hom, Functor.map_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply]
  rfl

omit [Fact (ringChar K ≠ l)] in
/-- The underlying pro-étale Weil sheaf of `π^* H`. -/
lemma weilSheaf_geometricFiberPullback_obj {H : AdicSheaf l X} [Fact (ringChar K ≠ l)]
    (hH : IsAdicLisseSheaf H) :
    (WeilSheaf.geometricFiberPullback (k₀ := K) hH).obj =
      (ProEtaleWeilSheaf.geometricFiberPullback K l X).obj H :=
  rfl

/-- The Weil structure of `π^* H` is the canonical identification `Fr^* π^* H ≅ π^* H`. -/
lemma adicFrobStr_geometricFiberPullback_hom_heq {H : AdicSheaf l X} (hH : IsAdicLisseSheaf H) :
    HEq (WeilSheaf.geometricFiberPullback (k₀ := K) hH).adicFrobStr.hom
      ((adicUpperStarComp l (X ↘ Spec (.of K)).geometricGaloisFrobenius.hom
          (X ↘ Spec (.of K)).geometricFiberProj).inv.app H ≫
        (adicUpperStarCongr l (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj
          (X ↘ Spec (.of K)))).hom.app H) := by
  rw [WeilSheaf.adicFrobStr, Iso.trans_hom, Iso.app_hom]
  refine HEq.trans (Endofunctor.IsoAlgebra.comp_str_hom_heq_of_eq _ _
    (pullbackStrIso (X ↘ Spec (.of K)).geometricGaloisFrobenius _
      (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj _)) H _ ?_) (heq_of_eq ?_)
  · rw [weilSheaf_geometricFiberPullback_obj,
      ProEtaleWeilSheaf.geometricFiberPullback_eq_functorOfNatIso]
  · rw [pullbackStrIso_hom_app, Iso.hom_inv_id_app_assoc, adicUpperStarFactorApp_inv,
      adicUpperStarFactor_inv_app]

/-- The Weil structure of `π^* H`, as a morphism of lisse sheaves. -/
lemma lisseFrobStr_geometricFiberPullback_hom (H : LisseSheaf l X) :
    ((WeilSheaf.geometricFiberPullback (k₀ := K) H.property).lisseFrobStr
        (WeilSheaf.isLisse_geometricFiberPullback H.property)).hom =
      LisseMonodromy.pullbackFrobLisseHom l (X ↘ Spec (.of K)).geometricGaloisFrobenius.hom
        (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj _) H :=
  ObjectProperty.hom_ext _ (eq_of_heq (adicFrobStr_geometricFiberPullback_hom_heq H.property))

/-- **Frobenius coherence of a pulled-back sheaf**: the transport of the stalk of `H` along the
arithmetic Frobenius `π_* β` is, through `H_{t ≫ π} ≅ (π^* H)_t`, the Frobenius `Φ` of the Weil
sheaf `π^* H`. -/
lemma upperStarStalkLinearEquiv_monoLinear_arithFrob
    (hc : LisseMonodromy.IsCompatible (X ↘ Spec (.of K)).geometricFiberProj M₀ M)
    (H : LisseSheaf l X)
    (v : LisseMonodromy.StalkSpace (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj) H) :
    LisseMonodromy.upperStarStalkLinearEquiv (X ↘ Spec (.of K)).geometricFiberProj B.t H
        (M₀.monoLinear B.arithFrob H v) =
      frobStalk M B (WeilSheaf.geometricFiberPullback (k₀ := K) H.property)
        (WeilSheaf.isLisse_geometricFiberPullback H.property)
        (LisseMonodromy.upperStarStalkLinearEquiv (X ↘ Spec (.of K)).geometricFiberProj B.t H
          v) := by
  rw [frobStalk_apply', lisseFrobStr_geometricFiberPullback_hom, arithFrob]
  exact LisseMonodromy.upperStarStalkLinearEquiv_monoLinear_pullbackPathIso_trans hc B.t _
    (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj _) B.frobPath
    (by rw [Category.assoc, Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj]) H v

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
    exact B.upperStarStalkLinearEquiv_monoLinear_arithFrob M₀ M hc H v

end FrobeniusBasePoint

end AlgebraicGeometry
