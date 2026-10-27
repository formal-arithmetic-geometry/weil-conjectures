/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PurityDiagonalBaseChangeCompared
public import Sheaf.Paper.SectionExceptionalFibreCoherence
import all Sheaf.Paper.SectionExceptionalFibreCoherence
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Logic.Small.Defs

/-! # Naturality of the section restriction of a dualizing exchange -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

private theorem pullback_comp_endpoint (A : Type (u + 1)) [CommRing A]
    {B X Z : Scheme.{u}} (v : Z ⟶ X) (p : X ⟶ B) (z : Z ⟶ B)
    (hz : z = v ≫ p) (K : Etale.DerivedCategoryModule A B) :
    (eqToIso (congrArg (fun r ↦ (Etale.ordinaryFinitePullback A r).obj K) hz)).hom ≫
        ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v p).app K).hom =
      ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v p z hz).app K).hom := by
  subst z
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp]

private theorem dualizing_base_congr (A : Type (u + 1)) [CommRing A] [Finite A]
    {B B' X X' : Scheme.{u}} {f : X ⟶ B} {f' : X' ⟶ B'}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    {v v' : X' ⟶ X} {b b' : B' ⟶ B}
    (sq : IsPullback v f' f b) (sq' : IsPullback v' f' f b')
    (hv : v = v') (hb : b = b') :
    Etale.dualizingComplexBaseChangeMap A sq =
      (eqToIso (congrArg (fun r ↦ (Etale.ordinaryFinitePullback A r).obj
        (Etale.dualizingComplex (ModuleCat.{u + 1} A) f)) hv)).hom ≫
        Etale.dualizingComplexBaseChangeMap A sq' := by
  subst v'
  subst b'
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp]

/-- Two factorizations of one Cartesian rectangle have the same dualizing exchange.
Source: smooth exceptional base change, adjunction mate pasting.
Proof: apply the base-change composition law to both factorizations, identify the
outer square by equality of its arrows, and cancel the first pullback compositor.

(blueprint: lem-pur-diagonal-exchange-naturality).
-/
theorem dualizing_base_rectangle (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X₁ X₂ X' B B₁ B₂ B' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X₁] [IsNoetherian X₂] [IsNoetherian X']
    [IsNoetherian B] [IsNoetherian B₁] [IsNoetherian B₂] [IsNoetherian B']
    {f : X ⟶ B} {f₁ : X₁ ⟶ B₁} {f₂ : X₂ ⟶ B₂} {f' : X' ⟶ B'}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f₁]
    [HasCompactification f₂] [HasCompactification f']
    [QuasiCompact f₁] [QuasiCompact f₂] [QuasiCompact f']
    {v₁ : X₁ ⟶ X} {v₂ : X₂ ⟶ X} {w₁ : X' ⟶ X₁} {w₂ : X' ⟶ X₂}
    {b₁ : B₁ ⟶ B} {b₂ : B₂ ⟶ B} {a₁ : B' ⟶ B₁} {a₂ : B' ⟶ B₂}
    (sq₁ : IsPullback v₁ f₁ f b₁) (sq₂ : IsPullback v₂ f₂ f b₂)
    (sq₁' : IsPullback w₁ f' f₁ a₁) (sq₂' : IsPullback w₂ f' f₂ a₂)
    (hv : w₁ ≫ v₁ = w₂ ≫ v₂) (hb : a₁ ≫ b₁ = a₂ ≫ b₂) :
    (Etale.ordinaryFinitePullback A w₁).map
        (Etale.dualizingComplexBaseChangeMap A sq₁) ≫
        Etale.dualizingComplexBaseChangeMap A sq₁' =
      ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w₁ v₁).inv.app
          (Etale.dualizingComplex (ModuleCat.{u + 1} A) f)) ≫
        ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
          w₂ v₂ (w₁ ≫ v₁) hv).hom.app
          (Etale.dualizingComplex (ModuleCat.{u + 1} A) f)) ≫
        (Etale.ordinaryFinitePullback A w₂).map
          (Etale.dualizingComplexBaseChangeMap A sq₂) ≫
        Etale.dualizingComplexBaseChangeMap A sq₂' := by
  have h₁ := Etale.dualizing_base_comp A sq₁ sq₁'
  have h₂ := Etale.dualizing_base_comp A sq₂ sq₂'
  have h₃ := dualizing_base_congr A (sq₁'.paste_horiz sq₁)
    (sq₂'.paste_horiz sq₂) hv hb
  rw [h₁, h₂] at h₃
  apply (cancel_epi ((Etale.leftDerivedUpperStarComp
    (ModuleCat.{u + 1} A) w₁ v₁).hom.app _)).1
  dsimp only [Etale.ordinaryFinitePullback]
  rw [h₃]
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  have he := pullback_comp_endpoint A w₂ v₂ (w₁ ≫ v₁) hv
    (Etale.dualizingComplex (ModuleCat.{u + 1} A) f)
  dsimp only [Etale.ordinaryFinitePullback, Iso.app_hom] at he
  rw [he]

/-- Restriction along compatible sections commutes with an inverse dualizing exchange.
This formal statement separates the section compositor from the geometric pasting equation.
Source: blueprint diagonal base-change comparison and inverse-image section coherence.
Proof: naturality moves the inverse exchange through the section-square compositor.
The assumed outer exchange equation cancels the two inverse exchanges. The remaining
identity is the inverse-image coherence equation for the two compatible sections.

(blueprint: lem-pur-diagonal-exchange-naturality).
-/
theorem section_inverse_exchange_naturality (A : Type (u + 1)) [CommRing A]
    {B B' W W' : Scheme.{u}} (a : B' ⟶ B) (p : W ⟶ B) (p' : W' ⟶ B')
    (v : W' ⟶ W) (s : B ⟶ W) (s' : B' ⟶ W')
    (hv : v ≫ p = p' ≫ a) (hs : s' ≫ v = a ≫ s)
    (h : s ≫ p = 𝟙 B) (h' : s' ≫ p' = 𝟙 B')
    (M : Etale.DerivedCategoryModule A B) (M' : Etale.DerivedCategoryModule A B')
    (N : Etale.DerivedCategoryModule A W) (N' : Etale.DerivedCategoryModule A W')
    (e : (Etale.ordinaryFinitePullback A p).obj M ≅ N)
    (e' : (Etale.ordinaryFinitePullback A p').obj M' ≅ N')
    (b : (Etale.ordinaryFinitePullback A a).obj M ≅ M')
    (c : (Etale.ordinaryFinitePullback A v).obj N ≅ N')
    (he : (Etale.ordinaryFinitePullback A v).mapIso e ≪≫ c =
      ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v p).symm.app M ≪≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p' a (v ≫ p) hv).app M) ≪≫
          (Etale.ordinaryFinitePullback A p').mapIso b ≪≫ e') :
    (Etale.ordinaryFinitePullback A a).mapIso
        ((Etale.ordinaryFinitePullback A s).mapIso e.symm ≪≫
          (Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) s p h).app M) ≪≫ b =
      Etale.sectionCoherencePullbackIso A a s s' v hs.symm N ≪≫
        (Etale.ordinaryFinitePullback A s').mapIso c ≪≫
        (Etale.ordinaryFinitePullback A s').mapIso e'.symm ≪≫
        (Etale.leftDerivedUpperStarCompSectionIso
          (ModuleCat.{u + 1} A) s' p' h').app M' := by
  let L := Etale.ordinaryFinitePullback A a
  let S := Etale.ordinaryFinitePullback A s
  let S' := Etale.ordinaryFinitePullback A s'
  let V := Etale.ordinaryFinitePullback A v
  let j := Etale.sectionCoherencePullbackIso A a s s' v hs.symm
  have hn := ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a s).symm ≪≫
    Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s' v (a ≫ s) hs.symm).hom.naturality
      e.inv
  simp only [Functor.comp_map] at hn
  have hc := Etale.leftDerivedUpperStar_map_comp_compSectionIso
    (ModuleCat.{u + 1} A) a p p' v s s' hv hs h h' M
  have hb := (Etale.leftDerivedUpperStarCompSectionIso
    (ModuleCat.{u + 1} A) s' p' h').hom.naturality b.hom
  simp only [Functor.comp_map, Functor.id_map] at hb
  have hei : c ≪≫ e'.symm =
      (V.mapIso e).symm ≪≫
        ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v p).symm.app M ≪≫
          (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
            p' a (v ≫ p) hv).app M) ≪≫
        (Etale.ordinaryFinitePullback A p').mapIso b := by
    calc
      _ = (V.mapIso e).symm ≪≫ ((V.mapIso e ≪≫ c) ≪≫ e'.symm) := by
        simp only [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans]
      _ = _ := by rw [he]; simp only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]
  apply Iso.ext
  simp only [Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc]
  have heih := congrArg Iso.hom hei
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.mapIso_inv] at heih
  rw [← S'.map_comp_assoc, heih]
  simp only [Functor.map_comp, Category.assoc]
  erw [← reassoc_of% hn]
  erw [hb]
  simp only [Functor.map_comp, Category.assoc] at hc
  erw [reassoc_of% hc]
  have hj := Etale.sectionPullback_endpoint A a s s' v (s' ≫ v) (a ≫ s)
    hs rfl rfl hs.symm ((Etale.ordinaryFinitePullback A p).obj M)
  have hji := congrArg Iso.inv hj
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.app_inv, NatTrans.comp_app] at hji
  dsimp only [Etale.ordinaryFinitePullback] at hji ⊢
  erw [reassoc_of% hji]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, NatTrans.comp_app,
    Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc]

end WeilConjectures.PurityFiniteSetting
