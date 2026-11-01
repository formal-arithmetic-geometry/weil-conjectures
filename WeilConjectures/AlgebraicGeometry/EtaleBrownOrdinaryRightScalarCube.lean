/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownProjectionRealization
import Mathlib.Tactic.CategoryTheory.Slice

/-! # Ordinary right-image realization and scalar restriction

Source: Zheng Construction 4.1 and Constructions 5.14--5.15; Stacks 03CV and 03CY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive

section OrdinaryRestriction

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
private theorem restriction_mate_underlying (N : B₀) :
    Ua.map ((mateEquiv a₀ a₁ (TwoSquare.mk _ _ _ _ β.hom)).natTrans.app N) ≫
        γ₁.hom.app (RB.obj N) ≫ V.map (rb.hom.app N) =
      ra.hom.app (G₀.obj N) ≫ γ₀.hom.app N := by
  let α := (mateEquiv a₀ a₁ (TwoSquare.mk _ _ _ _ β.hom)).natTrans
  change Ua.map (α.app N) ≫ γ₁.hom.app (RB.obj N) ≫ V.map (rb.hom.app N) = _
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
    dsimp only [Functor.comp_map, TwoSquare.natTrans]
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

end OrdinaryRestriction

private theorem sheaf_comp_apply
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    {R : Type*} [CommRing R] {M N P : Sheaf J (ModuleCat R)}
    (f : M ⟶ N) (g : N ⟶ P) (U : Cᵒᵖ) (x : M.obj.obj U) :
    ((f ≫ g).hom.app U) x = (g.hom.app U) ((f.hom.app U) x) := rfl

private theorem restrict_scalars_map_apply
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S)
    {M N : Sheaf J (ModuleCat.{u + 1} S)} (f : M ⟶ N) (U : Cᵒᵖ) (x : M.obj.obj U) :
    (((Sheaf.restrictScalars J φ).map f).hom.app U) x = (f.hom.app U) x := rfl

private theorem constant_module_map_apply
    (W : Scheme.{u}) (R : CommRingCat.{u + 1})
    {M N : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1} W.smallEtaleTopology
      ((constantSheaf W.smallEtaleTopology CommRingCat.{u + 1}).obj R)}
    (f : M ⟶ N) (U : W.Etaleᵒᵖ) (x : M.val.obj U) :
    (((Etale.SystemProjection.constantModule W R).map f).hom.app U) x =
      (f.val.app U) x := rfl

private theorem lower_star_map_apply
    {V W : Scheme.{u}} (g : V ⟶ W) (R : Type (u + 1)) [CommRing R]
    {M N : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} R)} (f : M ⟶ N)
    (U : W.Etaleᵒᵖ)
    (x : M.obj.obj ((MorphismProperty.Over.pullback @Etale ⊤ g).op.obj U)) :
    (((Etale.lowerStar (ModuleCat.{u + 1} R) g).map f).hom.app U) x =
      (f.hom.app ((MorphismProperty.Over.pullback @Etale ⊤ g).op.obj U)) x := rfl

attribute [local irreducible] CategoryTheory.mateEquiv

set_option maxHeartbeats 4000000 in
-- Section evaluation compares the fixed-ring and coefficient-level module categories.
/-- The normalized ordinary right-image comparison commutes with scalar restriction.
Source: Zheng Construction 4.1, Constructions 5.14--5.15 and Lemma 5.16;
Stacks 03CV and 03CY.
(blueprint: lem-pur-etale-brown-ordinary-right-scalar-cube).

Proof: transpose the inverse restriction square through the two level adjunctions.
The level Hom-transpose equations identify its underlying map: naturality of the
restriction isomorphisms, the inverse restriction normalization, and the counit
triangle give the ordinary restriction mate on underlying set sheaves. Evaluate
this equation on sections. Constant-scalar realization, restriction of scalars,
and geometric direct image have the recorded section maps. The normalizations of
q and the two ordinary restriction isomorphisms identify both paths. Extensionality
of module-sheaf morphisms then gives the asserted cube. No coefficient flatness or
condition on the geometric morphism is used. -/
theorem etaleBrownOrdinaryRightScalar_cube
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W) (A : StrictEtaleOrdinaryImage O t g)
    {PV : StrictEtaleEvaluation V O t} {PW : StrictEtaleEvaluation W O t}
    (RV : StrictEtaleBrownRealization O t V PV)
    (RW : StrictEtaleBrownRealization O t W PW)
    (q : ∀ n, A.right n ⋙ strictEtaleBrownConstant O t W n ≅
      strictEtaleBrownConstant O t V n ⋙
        Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g)
    (hq : ∀ n (M : strictEtaleLevel V O t n) (U : W.Etaleᵒᵖ)
      (x : ((A.right n).obj M).val.obj U),
      ((q n).hom.app M).hom.app U x =
        ((A.rightUnderlying n).hom.app M).hom.app U x)
    {m n : ℕ} (h : m ≤ n) (N : strictEtaleLevel V O t m) :
    (RW.val.ordinaryRestriction h).hom.app ((A.right m).obj N) ≫
        (Sheaf.restrictScalars W.smallEtaleTopology (strictEtaleBrownRingMap O t h)).map
          ((q m).hom.app N) =
      (strictEtaleBrownConstant O t W n).map
          ((mateEquiv (A.levelAdj m) (A.levelAdj n)
            (.mk _ _ _ _ (A.restrictInverse h).hom)).app N) ≫
        (q n).hom.app ((coefficientRestriction (J := V.smallEtaleTopology) O t h).obj N) ≫
        (Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g).map
          ((RV.val.ordinaryRestriction h).hom.app N) := by
  have ha := restriction_mate_underlying
    (A.lift m).modules (A.right m) (A.levelAdj m)
    (A.lift n).modules (A.right n) (A.levelAdj n)
    (coefficientRestriction (J := W.smallEtaleTopology) O t h)
    (coefficientRestriction (J := V.smallEtaleTopology) O t h)
    (coefficientUnderlying (J := W.smallEtaleTopology) O t n)
    (coefficientUnderlying (J := W.smallEtaleTopology) O t m)
    (coefficientUnderlying (J := V.smallEtaleTopology) O t n)
    (coefficientUnderlying (J := V.smallEtaleTopology) O t m)
    (Scheme.etaleSetPullback g) _ (strictEtaleSetAdjunction g)
    (coefficientRestrictionUnderlying (J := W.smallEtaleTopology) O t h)
    (coefficientRestrictionUnderlying (J := V.smallEtaleTopology) O t h)
    (A.lift m).moduleUnderlying (A.lift n).moduleUnderlying
    (A.rightUnderlying m) (A.rightUnderlying n) (A.restrictInverse h)
    (A.levelTranspose m) (A.levelTranspose n) (A.restrictInverseUnderlying h) N
  ext U x
  have hx := congrArg (fun f ↦ f.hom.app U x) ha
  erw [sheaf_comp_apply, sheaf_comp_apply, sheaf_comp_apply,
    restrict_scalars_map_apply, lower_star_map_apply, constant_module_map_apply]
  erw [eq_of_heq (RW.property.1 h _ U x), hq]
  erw [eq_of_heq (RV.property.1 h _ _ _), hq]
  exact hx.symm



end AlgebraicGeometry
