/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenDirectImageUnit
public import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.OrdinaryOpenCounitSquare

/-! # The underived mate for restriction to an inverse-image open

## References

* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- Elaborating the transported scheme module adjunctions needs this budget.
private theorem underived_open_mate
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) :
    (mateEquiv (schemeOpenModuleAdjunction X (f ⁻¹ᵁ V)) (schemeOpenModuleAdjunction Y V)
      (TwoSquare.mk _ _ _ _ (singleComplexOpenUnderivedDirectImageIso f V).hom)) =
      (schemeMVUnderivedOpenComposition f V).hom := by
  apply NatTrans.ext
  funext M
  apply ((schemeOpenModuleAdjunction Y V).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  have h := mateEquiv_counit
    (schemeOpenModuleAdjunction X (f ⁻¹ᵁ V)) (schemeOpenModuleAdjunction Y V)
    (TwoSquare.mk _ _ _ _ (singleComplexOpenUnderivedDirectImageIso f V).hom) M
  exact h.trans (schemeMVOrdinaryOpenCounit_square X Y f V M).symm

-- Elaborating the transported scheme module adjunctions needs this budget.
private theorem open_conjugate (X : Scheme.{u}) (V : X.Opens) :
    conjugateEquiv (schemeOpenModuleAdjunction X V)
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction V.ι))
      (openPinnedTensorOpenIso X V).hom = 𝟙 (Scheme.Modules.pushforward V.ι) := by
  apply NatTrans.ext
  funext M
  apply ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction V.ι)).homEquiv
    _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit,
    conjugateEquiv_counit]
  simp only [NatTrans.id_app,
    openPinnedTensorOpenIso, schemeOpenModuleAdjunction, Adjunction.ofNatIsoLeft_counit,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Category.assoc]
  rw [Scheme.Modules.restrictFunctorIsoPullback, Adjunction.leftAdjointUniq_inv_app,
    ← Category.assoc, Adjunction.leftAdjointUniq_trans_app]
  simp only [Iso.symm_inv, Iso.inv_hom_id_app_assoc]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact Adjunction.leftAdjointUniq_hom_app_counit
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction V.ι))
    (Scheme.Modules.restrictAdjunction V.ι) M

private theorem four_factor_conjugate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L₀ : C ⥤ D} {R₀ : D ⥤ C}
    {G G' : A ⥤ C} {S : C ⥤ A} {H H' : B ⥤ D} {T : D ⥤ B}
    {K : A ⥤ D} {Q : D ⥤ A}
    (a : L ⊣ R) (a₀ : L₀ ⊣ R₀) (b : G ⊣ S) (b' : G' ⊣ S)
    (c : H ⊣ T) (c' : H' ⊣ T) (d : K ⊣ Q)
    (s : G' ≅ G) (t : H' ≅ H) (x : K ≅ L ⋙ H') (y : K ≅ G' ⋙ L₀)
    (δ : T ⋙ R ≅ Q) (ε : R₀ ⋙ S ≅ Q)
    (hs : conjugateEquiv b b' s.hom = 𝟙 S)
    (ht : conjugateEquiv c c' t.hom = 𝟙 T)
    (hx : conjugateIsoEquiv (a.comp c') d x = δ)
    (hy : conjugateIsoEquiv (b'.comp a₀) d y = ε) :
    conjugateEquiv (a.comp c) (b.comp a₀)
      (Functor.isoWhiskerLeft L t.symm ≪≫ x.symm ≪≫ y ≪≫
        Functor.isoWhiskerRight s L₀).inv = δ.hom ≫ ε.inv := by
  have hsi : conjugateEquiv b' b s.inv = 𝟙 S := by
    have hi : conjugateIsoEquiv b b' s = Iso.refl _ := Iso.ext hs
    exact congrArg Iso.inv hi
  dsimp only [Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv]
  rw [← conjugateEquiv_comp _ (a.comp c'),
    ← conjugateEquiv_comp _ d, ← conjugateEquiv_comp _ (b'.comp a₀)]
  rw [conjugateEquiv_whiskerLeft c c' a, ht,
    conjugateEquiv_whiskerRight b' b a₀, hsi]
  have hxh := congrArg Iso.hom hx
  have hyi := congrArg Iso.inv hy
  change conjugateEquiv (a.comp c') d x.hom = δ.hom at hxh
  change conjugateEquiv d (b'.comp a₀) y.inv = ε.inv at hyi
  rw [hxh, hyi]
  simp

private theorem pushforward_congr_refl {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pushforwardCongr (rfl : f = f)).hom = 𝟙 (Scheme.Modules.pushforward f) := by
  ext M W
  simp

private theorem pushforward_congr_inv {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    (Scheme.Modules.pushforwardCongr h).inv =
      (Scheme.Modules.pushforwardCongr h.symm).hom := by
  subst g
  rfl

-- Match the chosen tensor adjunctions with the generic four-factor calculation.
private theorem tensor_open_conjugate
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) :
    conjugateEquiv
      ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)).comp
        (schemeOpenModuleAdjunction X (f ⁻¹ᵁ V)))
      ((schemeOpenModuleAdjunction Y V).comp
        (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ∣_ V))))
      (openPinnedTensorRestrictionIso f V (f ⁻¹ᵁ V) (f ∣_ V)
        (morphismRestrict_ι f V)).inv =
      (schemeMVUnderivedOpenComposition f V).hom := by
  classical
  let af := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)
  let a₀ := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ∣_ V))
  let aX := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ⁻¹ᵁ V).ι)
  let aY := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction V.ι)
  let aK := Classical.choose
    (Scheme.Modules.exists_tensorPullbackAdjunction ((f ⁻¹ᵁ V).ι ≫ f))
  let δ := Scheme.Modules.pushforwardComp (f ⁻¹ᵁ V).ι f ≪≫
    Scheme.Modules.pushforwardCongr (rfl : (f ⁻¹ᵁ V).ι ≫ f = (f ⁻¹ᵁ V).ι ≫ f)
  let ε := Scheme.Modules.pushforwardComp (f ∣_ V) V.ι ≪≫
    Scheme.Modules.pushforwardCongr (morphismRestrict_ι f V)
  let x := Scheme.Modules.tensorPullbackCompositionIso (f ⁻¹ᵁ V).ι f
    ((f ⁻¹ᵁ V).ι ≫ f) rfl
  let y := Scheme.Modules.tensorPullbackCompositionIso (f ∣_ V) V.ι
    ((f ⁻¹ᵁ V).ι ≫ f) (morphismRestrict_ι f V)
  have hx : conjugateIsoEquiv (af.comp aX) aK x = δ :=
    (conjugateIsoEquiv (af.comp aX) aK).apply_symm_apply δ
  have hy : conjugateIsoEquiv (aY.comp a₀) aK y = ε :=
    (conjugateIsoEquiv (aY.comp a₀) aK).apply_symm_apply ε
  have h := four_factor_conjugate af a₀ (schemeOpenModuleAdjunction Y V) aY
    (schemeOpenModuleAdjunction X (f ⁻¹ᵁ V)) aX aK
    (openPinnedTensorOpenIso Y V) (openPinnedTensorOpenIso X (f ⁻¹ᵁ V)) x y δ ε
    (open_conjugate Y V) (open_conjugate X (f ⁻¹ᵁ V)) hx hy
  change _ = δ.hom ≫ ε.inv at h
  refine h.trans ?_
  dsimp only [δ, ε, schemeMVUnderivedOpenComposition, Iso.trans_hom, Iso.trans_inv]
  rw [pushforward_congr_refl, pushforward_congr_inv]
  simp only [Category.comp_id, Iso.symm_hom]

-- The iterated mates law specializes four transported scheme module adjunctions.
/-- The sectionwise direct-image comparison is the mate of the inverse underived
restriction comparison. No complexes, derived categories, or additivity assumptions occur. -/
theorem singleComplexOpen_underived_tensor_mate
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) :
    (mateEquiv
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ∣_ V)))
      (TwoSquare.mk _ _ _ _
        (openPinnedTensorRestrictionIso f V (f ⁻¹ᵁ V) (f ∣_ V)
          (morphismRestrict_ι f V)).inv)) =
      (singleComplexOpenUnderivedDirectImageIso f V).hom := by
  apply (mateEquiv (schemeOpenModuleAdjunction X (f ⁻¹ᵁ V))
    (schemeOpenModuleAdjunction Y V)).injective
  exact (iterated_mateEquiv_conjugateEquiv
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ∣_ V)))
    (schemeOpenModuleAdjunction Y V) (schemeOpenModuleAdjunction X (f ⁻¹ᵁ V))
    (TwoSquare.mk _ _ _ _
      (openPinnedTensorRestrictionIso f V (f ⁻¹ᵁ V) (f ∣_ V)
        (morphismRestrict_ι f V)).inv)).trans
      ((tensor_open_conjugate f V).trans (underived_open_mate f V).symm)

end AlgebraicGeometry
