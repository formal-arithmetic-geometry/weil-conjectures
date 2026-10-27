/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B5
-/
module

public import Sheaf.DeligneLaumon.PoweredGeometricPullback
public import WeilConjectures.WeilSheaf.StalkFrobenius
import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence

/-! # First structure map of powered geometric pullback -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.WeilSheaf

private lemma iso_trans_app
    {A B : Type*} [Category A] [Category B] {F₀ F₁ F₂ F₃ : A ⥤ B}
    (α : F₀ ≅ F₁) (β : F₁ ≅ F₂) (γ : F₂ ≅ F₃) (e : F₀ ≅ F₃)
    (he : e = α ≪≫ β ≪≫ γ) (M : A) :
    e.hom.app M = α.hom.app M ≫ β.hom.app M ≫ γ.hom.app M := by
  rw [he]
  rfl

private lemma exchange_hom {Y Z : Scheme.{u}} (l : ℕ) [Fact l.Prime]
    (v : Z ⟶ Y) (a : Z ≅ Z) (b : Y ≅ Y)
    (h : a.hom ≫ v = v ≫ b.hom) (M : ProEtale.AdicSheaf l Y) :
    ((Functor.isoWhiskerLeft _ (ProEtale.adicUpperStarIsoLowerStarInv l a).symm ≪≫
      (ProEtale.adicUpperStarComp l _ _).symm ≪≫
      ProEtale.adicUpperStarCongr l h ≪≫ ProEtale.adicUpperStarComp l _ _ ≪≫
      Functor.isoWhiskerRight (ProEtale.adicUpperStarIsoLowerStarInv l b) _).hom.app M).hom =
      (ProEtale.upperStarIsoLowerStarInv _ a).inv.app ((v)^*ᵃ[l].obj M).X ≫
        (ProEtale.upperStarComp _ a.hom v).inv.app M.X ≫
        (ProEtale.upperStarCongr _ h).hom.app M.X ≫
        (ProEtale.upperStarComp _ v b.hom).hom.app M.X ≫
        (v)^*[_].map ((ProEtale.upperStarIsoLowerStarInv _ b).hom.app M.X) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Mod.comp_hom',
    ProEtale.adicUpperStar_map_hom, ProEtale.adicUpperStarIsoLowerStarInv_inv_app_hom,
    ProEtale.adicUpperStarIsoLowerStarInv_hom_app_hom,
    ProEtale.adicUpperStarComp_inv_app_hom, ProEtale.adicUpperStarComp_hom_app_hom,
    ProEtale.adicUpperStarCongr_hom_app_hom]

-- Keep functors and sheaves abstract while the kernel checks the carrier comparisons.
private lemma forget_map {Y : Scheme.{u}} {l : ℕ} [Fact l.Prime]
    {M N : ProEtale.AdicSheaf l Y} (f : M ⟶ N) :
    (ProEtale.AdicSheaf.forget Y).map f = f.hom := rfl

-- Keep both the functor and its output object as parameters during this computation.
private lemma mapped_structure
    {A B : Type*} [Category A] [Category B]
    {F₀ F : A ⥤ A} {H : B ⥤ B} {L : A ⥤ B}
    (φ : ∀ K : Endofunctor.IsoAlgebra F₀, F.obj K.carrier ≅ K.carrier)
    (hφ : ∀ {K K' : Endofunctor.IsoAlgebra F₀} (f : K ⟶ K'),
      F.map f.hom.f ≫ (φ K').hom = (φ K).hom ≫ f.hom.f)
    (e : L ⋙ H ≅ F ⋙ L) (S : Endofunctor.IsoAlgebra F₀ ⥤ Endofunctor.IsoAlgebra H)
    (hS : S = Endofunctor.IsoAlgebra.liftOfStr F φ hφ ⋙
      Endofunctor.IsoAlgebra.mapOfNatIso e)
    (K : Endofunctor.IsoAlgebra F₀) (P : Endofunctor.IsoAlgebra H)
    (hP : P = S.obj K) (h : P.carrier = L.obj K.carrier) :
    H.map (eqToIso h.symm).hom ≫ P.str.hom =
      e.hom.app K.carrier ≫ L.map (φ K).hom ≫ (eqToIso h.symm).hom := by
  subst S P
  change H.map (𝟙 (L.obj K.carrier)) ≫
    ((Endofunctor.IsoAlgebra.liftOfStr F φ hφ ⋙
      Endofunctor.IsoAlgebra.mapOfNatIso e).obj K).str.hom =
        e.hom.app K.carrier ≫ L.map (φ K).hom ≫ (𝟙 (L.obj K.carrier))
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
    Endofunctor.IsoAlgebra.liftOfStr_comp_mapOfNatIso_obj_str, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom]

private lemma exchange_structure {Y Z : Scheme.{u}} (l : ℕ) [Fact l.Prime]
    (v : Z ⟶ Y) (a : Z ≅ Z) (b : Y ≅ Y)
    (M : ProEtale.AdicSheaf l Y) (N : ProEtale.AdicSheaf l Z)
    (φ : (b.inv)_*ᵃ[l].obj M ≅ M) (ψ : (a.inv)_*ᵃ[l].obj N ≅ N)
    (θ : (v)^*ᵃ[l].obj M ⟶ N)
    (e : (v)^*ᵃ[l] ⋙ (a.inv)_*ᵃ[l] ≅ (b.inv)_*ᵃ[l] ⋙ (v)^*ᵃ[l])
    (hθ : (a.inv)_*ᵃ[l].map θ ≫ ψ.hom =
      e.hom.app M ≫ (v)^*ᵃ[l].map φ.hom ≫ θ)
    (H : Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l) ⥤
      Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l))
    (α : H ≅ (a.inv)_*[WeilCoefficients.{u} l])
    (E : H.obj ((v)^*[_].obj M.X) ⟶ (v)^*[_].obj ((b.hom)^*[_].obj M.X))
    {S₁ S₂ : Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)}
    (c₁ : H.obj ((v)^*[_].obj M.X) ⟶ S₁) (c₂ : S₁ ⟶ S₂)
    (c₃ : S₂ ⟶ (v)^*[_].obj ((b.hom)^*[_].obj M.X))
    (hE : E = c₁ ≫ c₂ ≫ c₃)
    (he : (e.hom.app M).hom = α.inv.app ((v)^*ᵃ[l].obj M).X ≫ c₁ ≫ c₂ ≫ c₃ ≫
      (v)^*[_].map ((ProEtale.upperStarIsoLowerStarInv _ b).hom.app M.X)) :
    @Eq (H.obj ((v)^*[WeilCoefficients.{u} l].obj M.X) ⟶ N.X)
      (H.map (X := (v)^*[WeilCoefficients.{u} l].obj M.X) (Y := N.X)
          ((ProEtale.AdicSheaf.forget Z).map θ) ≫ α.hom.app N.X ≫
        (ProEtale.AdicSheaf.forget Z).map ψ.hom)
      (E ≫ @CategoryStruct.comp _ _
        ((v)^*[_].obj ((b.hom)^*[_].obj M.X)) ((v)^*[_].obj M.X) N.X
        ((v)^*[_].map ((ProEtale.upperStarIsoLowerStarInv _ b).hom.app M.X ≫
          (ProEtale.AdicSheaf.forget Y).map φ.hom))
        ((ProEtale.AdicSheaf.forget Z).map θ)) := by
  simp only [forget_map]
  have n := α.hom.naturality θ.hom
  have h := congrArg (fun f ↦ f.hom) hθ
  simp only [Mod.comp_hom', ProEtale.adicLowerStar_map_hom,
    ProEtale.adicUpperStar_map_hom] at h
  rw [reassoc_of% n, h, he, hE]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Functor.map_comp]

variable {k₀ k₁ : Type u} [Field k₀] [Finite k₀] [Field k₁] [Finite k₁]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] [Fact (ringChar k₁ ≠ l)]
  {X C : Scheme.{u}} [X.Over (Spec (.of k₀))] [C.Over (Spec (.of k₁))]
  (v : (C ↘ Spec (.of k₁)).geometricFiber ⟶ (X ↘ Spec (.of k₀)).geometricFiber)
  (r : ℕ)
  (hv : (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom ≫ v =
    v ≫ ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r).hom)

omit [Fact (ringChar k₀ ≠ l)] [Fact (ringChar k₁ ≠ l)] in
private lemma powered_comm_eq : poweredGeometricPullbackCommIso (l := l) v r hv =
    Functor.isoWhiskerLeft _ (ProEtale.adicUpperStarIsoLowerStarInv l
      (C ↘ Spec (.of k₁)).geometricGaloisFrobenius).symm ≪≫
      (ProEtale.adicUpperStarComp l _ _).symm ≪≫ ProEtale.adicUpperStarCongr l hv ≪≫
        ProEtale.adicUpperStarComp l _ _ ≪≫
          Functor.isoWhiskerRight (ProEtale.adicUpperStarIsoLowerStarInv l
            ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r)) _ := by
  unfold poweredGeometricPullbackCommIso
  rfl

omit [Fact (ringChar k₀ ≠ l)] [Fact (ringChar k₁ ≠ l)] in
private lemma powered_all_eq : poweredGeometricPullbackAll (l := l) v r hv =
    Endofunctor.IsoAlgebra.liftOfStr
      (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X r)
      (fun K : ProEtaleWeilSheaf k₀ l X ↦ K.frobeniusPowIso r)
      (fun f ↦ ProEtaleWeilSheaf.frobeniusPowIso_hom_naturality f r) ⋙
        Endofunctor.IsoAlgebra.mapOfNatIso (poweredGeometricPullbackCommIso v r hv) := by
  unfold poweredGeometricPullbackAll ProEtaleWeilSheaf.powFunctor
  rfl

private lemma powered_obj_eq_all (G : WeilSheaf k₀ l X) :
    ((poweredGeometricPullback v r hv).obj G).obj =
      (poweredGeometricPullbackAll v r hv).obj G.obj := by
  unfold poweredGeometricPullback
  rfl

private lemma powered_adic_first (G : WeilSheaf k₀ l X) :
    (frobeniusPullback k₁ l C).map
        (eqToIso (poweredGeometricPullback_obj_carrier v r hv G).symm).hom ≫
      ((poweredGeometricPullback v r hv).obj G).obj.str.hom =
    (poweredGeometricPullbackCommIso v r hv).hom.app G.obj.carrier ≫
      (v)^*ᵃ[l].map (G.obj.frobeniusPowIso r).hom ≫
        (eqToIso (poweredGeometricPullback_obj_carrier v r hv G).symm).hom := by
  exact mapped_structure (fun K : ProEtaleWeilSheaf k₀ l X ↦ K.frobeniusPowIso r)
    (fun f ↦ ProEtaleWeilSheaf.frobeniusPowIso_hom_naturality f r)
    (poweredGeometricPullbackCommIso v r hv) (poweredGeometricPullbackAll v r hv)
    (powered_all_eq v r hv) G.obj ((poweredGeometricPullback v r hv).obj G).obj
    (powered_obj_eq_all v r hv G) (poweredGeometricPullback_obj_carrier v r hv G)

omit [Fact (ringChar k₁ ≠ l)] in
private lemma powered_comm_hom (G : WeilSheaf k₀ l X) :
    ((poweredGeometricPullbackCommIso v r hv).hom.app G.obj.carrier).hom =
      (ProEtale.upperStarIsoLowerStarInv _
        (C ↘ Spec (.of k₁)).geometricGaloisFrobenius).inv.app
          ((v)^*ᵃ[l].obj G.obj.carrier).X ≫
        (ProEtale.upperStarComp _
          (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom v).inv.app G.obj.carrier.X ≫
        (ProEtale.upperStarCongr _ hv).hom.app G.obj.carrier.X ≫
        (ProEtale.upperStarComp _ v
          ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r).hom).hom.app G.obj.carrier.X ≫
        (v)^*[_].map ((ProEtale.upperStarIsoLowerStarInv _
          ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r)).hom.app G.obj.carrier.X) :=
  (congrArg (fun i ↦ (i.hom.app G.obj.carrier).hom) (powered_comm_eq v r hv)).trans
    (exchange_hom l v (C ↘ Spec (.of k₁)).geometricGaloisFrobenius
      ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r) hv G.obj.carrier)

/-- The explicit powered pullback intertwines its first Weil map with the r-fold source map.

Source: blueprint `thm-zl-real-mixed-by-curves.proof.md`, paragraphs 1--3
(blueprint: lem-zl-powered-geometric-pullback-first-structure).

Proof: Compute the structure of the composite of powFunctor and mapOfNatIso using the generic
algebra construction, retaining the functor and output object as parameters. Forget its adic
exchange isomorphism to sheaves. Naturality of the upperStarIsoLowerStarInv comparison moves
the carrier identification across that comparison; the adjacent comparison and its inverse
cancel. The remaining source comparison followed by the r-fold adic Weil map is precisely
frobeniusPowStr r. Group the three pullback compositors into upperStarCompIso. All carrier
identifications are the original ones, and the calculation also applies when r=0. -/
theorem poweredGeometricPullback_firstStructure (G : WeilSheaf k₀ l X) :
    @Eq ((((C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom)^*[_]).obj
      ((v)^*[WeilCoefficients.{u} l].obj G.obj.carrier.X) ⟶
        ((poweredGeometricPullback v r hv).obj G).obj.carrier.X)
      (((C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom)^*[_].map
          (X := (v)^*[WeilCoefficients.{u} l].obj G.obj.carrier.X)
          ((ProEtale.AdicSheaf.forget _).map
            (eqToIso (poweredGeometricPullback_obj_carrier v r hv G).symm).hom) ≫
        ((poweredGeometricPullback v r hv).obj G).frobeniusStr)
      ((ProEtale.upperStarCompIso _ hv).hom.app G.obj.carrier.X ≫
        @CategoryStruct.comp _ _
          ((v)^*[_].obj ((((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r).hom)^*[_].obj
            G.obj.carrier.X)) ((v)^*[_].obj G.obj.carrier.X)
          ((poweredGeometricPullback v r hv).obj G).obj.carrier.X
          ((v)^*[_].map (G.frobeniusPowStr r))
          ((ProEtale.AdicSheaf.forget _).map
            (eqToIso (poweredGeometricPullback_obj_carrier v r hv G).symm).hom)) := by
  let P := (poweredGeometricPullback v r hv).obj G
  let Θ := eqToIso (poweredGeometricPullback_obj_carrier v r hv G).symm
  have hθ := powered_adic_first v r hv G
  have hE := iso_trans_app
    (ProEtale.upperStarComp (WeilCoefficients.{u} l)
      (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom v).symm
    (ProEtale.upperStarCongr _ hv)
    (ProEtale.upperStarComp _ v ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r).hom)
    (ProEtale.upperStarCompIso _ hv) rfl G.obj.carrier.X
  have h := exchange_structure l v
    (C ↘ Spec (.of k₁)).geometricGaloisFrobenius
    ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r)
    G.obj.carrier P.obj.carrier (G.obj.frobeniusPowIso r) P.obj.str Θ.hom
    (poweredGeometricPullbackCommIso v r hv) hθ
    (((C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom)^*[_])
    (ProEtale.upperStarIsoLowerStarInv _
      (C ↘ Spec (.of k₁)).geometricGaloisFrobenius)
    ((ProEtale.upperStarCompIso _ hv).hom.app G.obj.carrier.X)
    ((ProEtale.upperStarComp _
      (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom v).inv.app G.obj.carrier.X)
    ((ProEtale.upperStarCongr _ hv).hom.app G.obj.carrier.X)
    ((ProEtale.upperStarComp _ v
      ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r).hom).hom.app G.obj.carrier.X)
    hE (powered_comm_hom v r hv G)
  simpa only [frobeniusStr,
    frobeniusPowStr, frobeniusPowIso_eq, P, Θ, Category.assoc] using h

end AlgebraicGeometry.WeilSheaf
