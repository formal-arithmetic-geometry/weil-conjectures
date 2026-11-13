/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownProjectionRealization

/-! # The ordinary restriction and Brown image cube

Source: Zheng, Construction 4.1 and Lemma 5.16; Stacks 03CV and 03CZ.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive
section OrdinaryRightCube

universe a₀v a₁v b₀v b₁v xv yv a₀u a₁u b₀u b₁u xu yu
variable {A₀ : Type a₀u} [Category.{a₀v} A₀] {A₁ : Type a₁u} [Category.{a₁v} A₁]
  {B₀ : Type b₀u} [Category.{b₀v} B₀] {B₁ : Type b₁u} [Category.{b₁v} B₁]
  {X : Type xu} [Category.{xv} X] {Y : Type yu} [Category.{yv} Y]
  (F₀ : A₀ ⥤ B₀) (G₀ : B₀ ⥤ A₀) (a₀ : F₀ ⊣ G₀)
  (F₁ : A₁ ⥤ B₁) (G₁ : B₁ ⥤ A₁) (a₁ : F₁ ⊣ G₁)
  (RA : A₀ ⥤ A₁) (RB : B₀ ⥤ B₁)
  (Ua : A₁ ⥤ X) (Un : A₀ ⥤ X) (Ub : B₁ ⥤ Y) (Uq : B₀ ⥤ Y)
  (L : X ⥤ Y) (V : Y ⥤ X) (adj : L ⊣ V)
  (ra : RA ⋙ Ua ≅ Un) (rb : RB ⋙ Ub ≅ Uq)
  (mu₀ : F₀ ⋙ Uq ≅ Un ⋙ L) (mu₁ : F₁ ⋙ Ub ≅ Ua ⋙ L)
  (γ₀ : G₀ ⋙ Un ≅ Uq ⋙ V) (γ₁ : G₁ ⋙ Ua ≅ Ub ⋙ V)
  (β : RA ⋙ F₁ ≅ F₀ ⋙ RB)
  (h₀ : ∀ M N (f : F₀.obj M ⟶ N),
    Un.map (a₀.homEquiv M N f) ≫ γ₀.hom.app N =
      adj.homEquiv _ _ (mu₀.inv.app M ≫ Uq.map f))
  (h₁ : ∀ M N (f : F₁.obj M ⟶ N),
    Ua.map (a₁.homEquiv M N f) ≫ γ₁.hom.app N =
      adj.homEquiv _ _ (mu₁.inv.app M ≫ Ub.map f))
  (hβ : ∀ M, Ub.map (β.hom.app M) ≫ rb.hom.app (F₀.obj M) ≫ mu₀.hom.app M =
    mu₁.hom.app (RA.obj M) ≫ L.map (ra.hom.app M))

include h₀ h₁ hβ in
private theorem ordinary_restriction_mate (N : B₀) :
    Ua.map ((mateEquiv a₀ a₁ (.mk _ _ _ _ β.hom)).app N) ≫
        γ₁.hom.app (RB.obj N) ≫ V.map (rb.hom.app N) =
      ra.hom.app (G₀.obj N) ≫ γ₀.hom.app N := by
  let α := (mateEquiv a₀ a₁ (.mk _ _ _ _ β.hom))
  let M := G₀.obj N
  let ε := a₀.counit.app N
  have ha : α.app N = a₁.homEquiv _ _
      (β.hom.app M ≫ RB.map ε) := by
    dsimp only [α, mateEquiv, TwoSquare.mk,
      Equiv.coe_fn_mk, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.rightUnitor_inv_app,
      Functor.leftUnitor_hom_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.comp_obj]
    simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.id_comp]
    dsimp only [Functor.comp_map]
    erw [Category.comp_id]
  rw [ha]
  erw [← Category.assoc, h₁]
  rw [← adj.homEquiv_naturality_right]
  apply (adj.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply]
  have hb := rb.hom.naturality ε
  change Ub.map (RB.map ε) ≫ rb.hom.app N =
    rb.hom.app (F₀.obj M) ≫ Uq.map ε at hb
  simp only [Functor.map_comp, Category.assoc]
  rw [hb]
  have hi := hβ M
  have hi' : mu₁.inv.app (RA.obj M) ≫
      Ub.map (β.hom.app M) ≫
      rb.hom.app (F₀.obj M) =
    L.map (ra.hom.app M) ≫ mu₀.inv.app M := by
    apply (cancel_epi (mu₁.hom.app (RA.obj M))).1
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    apply (cancel_mono (mu₀.hom.app M)).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    exact hi
  dsimp only [Functor.comp_obj]
  slice_lhs 1 3 => exact hi'
  rw [Category.assoc]
  rw [Adjunction.homEquiv_naturality_left_symm]
  have hε : a₀.homEquiv M N ε = 𝟙 M := by
    rw [Adjunction.homEquiv_unit, a₀.right_triangle_components]
  have hn := h₀ M N ε
  rw [hε] at hn
  erw [Un.map_id M, Category.id_comp] at hn
  erw [hn, Equiv.symm_apply_apply]

end OrdinaryRightCube
set_option maxHeartbeats 8000000 in
-- Specializing the mate checks the concrete coefficient categories.
/-- The underlying ordinary Brown mate after restriction. -/
private theorem brown_underlying_cube
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W)
    (A : StrictEtaleOrdinaryImage O t g)
    {m n : ℕ} (h : m ≤ n) (M : strictEtaleLevel V O t m) :
    (coefficientUnderlying (J := W.smallEtaleTopology) O t n).map
        ((mateEquiv (A.levelAdj m) (A.levelAdj n)
          (.mk _ _ _ _ (A.restrictInverse h).hom)).app M) ≫
      (A.rightUnderlying n).hom.app
        ((coefficientRestriction (J := V.smallEtaleTopology) O t h).obj M) ≫
      ((MorphismProperty.Over.pullback @Etale ⊤ g).sheafPushforwardContinuous
        (Type (u + 1)) _ _).map
        ((coefficientRestrictionUnderlying (J := V.smallEtaleTopology) O t h).hom.app M) =
    (coefficientRestrictionUnderlying (J := W.smallEtaleTopology) O t h).hom.app
        ((A.right m).obj M) ≫ (A.rightUnderlying m).hom.app M := by
  exact ordinary_restriction_mate
    (A.lift m).modules (A.right m) (A.levelAdj m)
    (A.lift n).modules (A.right n) (A.levelAdj n)
    (coefficientRestriction (J := W.smallEtaleTopology) O t h)
    (coefficientRestriction (J := V.smallEtaleTopology) O t h)
    (coefficientUnderlying (J := W.smallEtaleTopology) O t n)
    (coefficientUnderlying (J := W.smallEtaleTopology) O t m)
    (coefficientUnderlying (J := V.smallEtaleTopology) O t n)
    (coefficientUnderlying (J := V.smallEtaleTopology) O t m)
    _ _ (strictEtaleSetAdjunction g)
    (coefficientRestrictionUnderlying (J := W.smallEtaleTopology) O t h)
    (coefficientRestrictionUnderlying (J := V.smallEtaleTopology) O t h)
    (A.lift m).moduleUnderlying (A.lift n).moduleUnderlying
    (A.rightUnderlying m) (A.rightUnderlying n) (A.restrictInverse h)
    (A.levelTranspose m) (A.levelTranspose n) (A.restrictInverseUnderlying h) M

set_option maxHeartbeats 8000000 in
-- Check the section calculation independently of the derived assembly.
/-- The ordinary Brown restriction/image cube, before deriving.
Source: Zheng, Construction 4.1 and Lemma 5.16; Stacks 03CV and 03CZ.
(blueprint: lem-pur-brown-ordinary-restriction-cube).
Proof: transpose the inverse-image restriction square using the two ordinary
adjunctions. The underlying-set Hom formulas identify its transpose with the
set-sheaf direct-image restriction identity. Evaluate at an etale object and a
section; the Brown image section equations and the scalar restriction section
equations identify the two routes. No properness or finite-coefficient hypothesis
is used, including for identity coefficient transitions and the zero ring. -/
theorem etaleBrownOrdinaryRestrictionCube
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W)
    (A : StrictEtaleOrdinaryImage O t g)
    (PW : StrictEtaleEvaluation W O t) (PV : StrictEtaleEvaluation V O t)
    (B : CoefficientSystemDerivedImage (J := W.smallEtaleTopology)
      (K := V.smallEtaleTopology) O t _ _ _ A PW PV)
    (RV : StrictEtaleBrownRealization O t V PV)
    (RW : StrictEtaleBrownRealization O t W PW)
    (rg : ∀ n, StrictEtaleBrownImageRealization O t g n A (B.level n) RV RW)
    {m n : ℕ} (h : m ≤ n) (M : strictEtaleLevel V O t m) :
      (RW.val.ordinaryRestriction h).hom.app ((A.right m).obj M) ≫
          (Functor.whiskerRight (rg m).val.ordinaryRight.hom (Sheaf.restrictScalars
      W.smallEtaleTopology (strictEtaleBrownRingMap O t h)) ≫
            Functor.whiskerLeft (strictEtaleBrownConstant O t V m)
      (Etale.lowerStarRestrictScalarsIso (strictEtaleBrownRingMap O t h) g).hom).app M =
        (Functor.whiskerRight ((mateEquiv (A.levelAdj m) (A.levelAdj n) (.mk _ _ _ _
      (A.restrictInverse h).hom))) (strictEtaleBrownConstant O t W n) ≫
          Functor.whiskerLeft (coefficientRestriction.{u + 1, u, u + 1} (J := V.smallEtaleTopology)
      O t h) (rg n).val.ordinaryRight.hom).app M ≫
            (Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g).map
      ((RV.val.ordinaryRestriction h).hom.app M) := by
  let qV := coefficientRestriction.{u + 1, u, u + 1} (J := V.smallEtaleTopology) O t h
  let α := (mateEquiv (A.levelAdj m) (A.levelAdj n)
    (.mk _ _ _ _ (A.restrictInverse h).hom))
  have ho := brown_underlying_cube O t g A h M
  ext U x
  have hox := congrArg (fun k ↦ (k.hom.app U) x) ho
  change ((A.rightUnderlying n).hom.app (qV.obj M)).hom.app U
      ((α.app M).val.app U x) = ((A.rightUnderlying m).hom.app M).hom.app U x at hox
  change ((rg m).val.ordinaryRight.hom.app M).hom.app U
      (((RW.val.ordinaryRestriction h).hom.app ((A.right m).obj M)).hom.app U x) =
    (((RV.val.ordinaryRestriction h).hom.app M).hom.app _)
      (((rg n).val.ordinaryRight.hom.app (qV.obj M)).hom.app U
        ((α.app M).val.app U x))
  calc
    _ = ((rg m).val.ordinaryRight.hom.app M).hom.app U x :=
      congrArg (fun y ↦ ((rg m).val.ordinaryRight.hom.app M).hom.app U y)
        (eq_of_heq (RW.property.1 h _ U x))
    _ = ((A.rightUnderlying m).hom.app M).hom.app U x := (rg m).property.1 M U x
    _ = ((A.rightUnderlying n).hom.app (qV.obj M)).hom.app U
        ((α.app M).val.app U x) := hox.symm
    _ = ((rg n).val.ordinaryRight.hom.app (qV.obj M)).hom.app U
        ((α.app M).val.app U x) := ((rg n).property.1 _ U _).symm
    _ = _ := (eq_of_heq (RV.property.1 h M _ _)).symm

end AlgebraicGeometry
