/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenScalarSupport
import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearScalarDerivedComparison
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenScalarSupport
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenCore
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.Normalization.SemilinearProperOpenNormalization
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.Normalization.ExactClopenNormalization
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! # Scalar compatibility of the intrinsic inverse-image clopen word

Source: Stacks Project, Tag 0F7B, open case; Zheng, Construction 4.1 and Lemma 4.10.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option synthInstance.maxSize 64
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen
open Normalization
variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
variable (B : Type (u + 1)) [CommRing B]
  (φ : ∀ n : ℕ, B →+* C n)
  (hφ : ∀ n : ℕ, (τ n).hom.comp (φ (n + 1)) = φ n)

section NormalizedComparison
attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.mapDerivedCategoryNatIso Functor.mapDerivedCategoryCompIso
  Functor.mapDerivedCategoryFactors Functor.rightDerivedFunctor HasDerivedCategory.standard
  constantSheaf DerivedCategory.Q rhoOrdinary alpha gamma
  WeilConjectures.SemilinearSections.systemRing coefficientMap VaryingRing.ringMap
attribute [local implicit_reducible] VaryingRing.ordinaryScalarMap
  VaryingRing.coefficientTransition
attribute [local instance] VaryingRing.push_isRightAdjoint VaryingRing.push_additive
  VaryingRing.pullAdditive VaryingRing.pullLimits VaryingRing.pullColimits
attribute [local instance] rho_additive rho_limits rho_colimits

/-- Localize a section-normalized identification of the ordinary scalar functors. -/
private def localized_scalar_iso
    (D : VaryingRing.OrdinaryScalarComparison C τ B
      (fun n ↦ CommRingCat.ofHom (φ n))) (X : Scheme.{u})
    (a : D.rho X ≅ rhoOrdinary C τ B φ hφ X) :
    VaryingRing.scalarRho D X ≅ rho C τ B φ hφ X := by
  let rA : (rhoOrdinary C τ B φ hφ X).Additive := rho_additive C τ B φ hφ X
  let rL : PreservesFiniteLimits (rhoOrdinary C τ B φ hφ X) := rho_limits C τ B φ hφ X
  let rC : PreservesFiniteColimits (rhoOrdinary C τ B φ hφ X) := rho_colimits C τ B φ hφ X
  let dA : (D.rho X).Additive := D.additive X
  let dL : PreservesFiniteLimits (D.rho X) := D.limits X
  let dC : PreservesFiniteColimits (D.rho X) := D.colimits X
  exact Functor.mapDerivedCategoryNatIso a

/-- Localize an ordinary scalar/pullback square with its exactness instances fixed. -/
private def localized_pull_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : Modules C τ Y ⥤ Modules C τ X) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (s : rhoOrdinary C τ B φ hφ Y ⋙ StrictTower.towerPullback B f ≅
      L ⋙ rhoOrdinary C τ B φ hφ X) :
    rho C τ B φ hφ Y ⋙ StrictTower.G B f ≅
      L.mapDerivedCategory ⋙ rho C τ B φ hφ X := by
  let rAX : (rhoOrdinary C τ B φ hφ X).Additive := rho_additive C τ B φ hφ X
  let rAY : (rhoOrdinary C τ B φ hφ Y).Additive := rho_additive C τ B φ hφ Y
  let rLX : PreservesFiniteLimits (rhoOrdinary C τ B φ hφ X) := rho_limits C τ B φ hφ X
  let rLY : PreservesFiniteLimits (rhoOrdinary C τ B φ hφ Y) := rho_limits C τ B φ hφ Y
  let rCX : PreservesFiniteColimits (rhoOrdinary C τ B φ hφ X) := rho_colimits C τ B φ hφ X
  let rCY : PreservesFiniteColimits (rhoOrdinary C τ B φ hφ Y) := rho_colimits C τ B φ hφ Y
  exact Functor.mapDerivedCategorySquareIso s

/-- Identity on sections identifies the chosen direct-image square and hence its mate. -/
private theorem normalized_pull
    (D : VaryingRing.OrdinaryScalarComparison C τ B
      (fun n ↦ CommRingCat.ofHom (φ n)))
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (aX : D.rho X ≅ rhoOrdinary C τ B φ hφ X)
    (aY : D.rho Y ≅ rhoOrdinary C τ B φ hφ Y)
    (haX : ∀ (M : Modules C τ X) (n : ℕ) (H : X.ProEtᵒᵖ)
      (x : (((D.rho X).obj M).obj (op n)).val.obj H),
      HEq (((aX.hom.app M).app (op n)).val.app H x) x)
    (haY : ∀ (M : Modules C τ Y) (n : ℕ) (H : Y.ProEtᵒᵖ)
      (x : (((D.rho Y).obj M).obj (op n)).val.obj H),
      HEq (((aY.hom.app M).app (op n)).val.app H x) x)
    (F : Modules C τ X ⥤ Modules C τ Y) [F.IsRightAdjoint]
    (hF : F = VaryingRing.push C τ f)
    (e : rhoOrdinary C τ B φ hφ X ⋙ StrictTower.towerDirectImage B f ≅
      F ⋙ rhoOrdinary C τ B φ hφ Y)
    (he : ∀ (M : Modules C τ X) (n : ℕ) (U : Y.ProEt),
      HEq (fun x ↦ ((e.hom.app M).app (op n)).val.app (op U) x)
        (fun x : M.val.obj (op (n, (Scheme.proEtaleBaseChange f).obj U)) ↦ x)) :
    HEq ((mateEquiv (Adjunction.ofIsRightAdjoint F)
      (VaryingRing.scalarTowerAdj B f)).symm (TwoSquare.mk _ _ _ _ e.inv)).natTrans
      (Functor.whiskerRight aY.inv (StrictTower.towerPullback B f) ≫
        (D.b f).inv ≫ Functor.whiskerLeft (VaryingRing.pull C τ f) aX.hom) := by
  subst F
  let d := Functor.isoWhiskerLeft (VaryingRing.push C τ f) aY.symm ≪≫
    D.d f ≪≫ Functor.isoWhiskerRight aX (StrictTower.towerDirectImage B f)
  have hd : d.hom = e.inv := by
    apply (cancel_mono e.hom).mp
    erw [e.inv_hom_id]
    apply NatTrans.ext
    funext M
    apply NatTrans.ext
    funext n
    ext U x
    let y := (((aY.inv.app ((VaryingRing.push C τ f).obj M)).app n).val.app U) x
    let z := ((((D.d f).hom.app M).app n).val.app U) y
    let t := (((aX.hom.app M).app n).val.app
      ((Scheme.proEtaleBaseChange f).op.obj U)) z
    have hy : HEq y x := normalized_inverse
      (fun q ↦ (((aY.hom.app ((VaryingRing.push C τ f).obj M)).app n).val.app U) q)
      (fun q ↦ (((aY.inv.app ((VaryingRing.push C τ f).obj M)).app n).val.app U) q)
      (fun q ↦ congrArg (fun v ↦ (v.app n).val.app U q)
        (aY.inv_hom_id_app ((VaryingRing.push C τ f).obj M)))
      (haY ((VaryingRing.push C τ f).obj M) n.unop U) x
    have hz := D.d_sections f M n.unop U y
    have ht := haX M n.unop ((Scheme.proEtaleBaseChange f).op.obj U) z
    have hh := normalized_apply
      (rho_section_type C τ B φ hφ X M n.unop
        ((Scheme.proEtaleBaseChange f).obj U.unop))
      (rho_section_type C τ B φ hφ Y ((VaryingRing.push C τ f).obj M) n.unop U.unop)
      _ (he M n.unop U.unop) t
    exact eq_of_heq (hh.trans (ht.trans (hz.trans hy)))
  let w := ((TwoSquare.mk _ _ _ _ (D.b f).inv).whiskerTop aY.inv).whiskerBottom aX.hom
  have hw : mateEquiv (VaryingRing.moduleAdj C τ f)
      (VaryingRing.scalarTowerAdj B f) w = TwoSquare.mk _ _ _ _ d.hom := by
    dsimp only [w]
    erw [mateEquiv_whiskerTop_whiskerBottom]
    apply TwoSquare.ext
    intro N
    change aY.inv.app ((VaryingRing.push C τ f).obj N) ≫
      (mateEquiv (VaryingRing.moduleAdj C τ f) (VaryingRing.scalarTowerAdj B f)
        (D.b f).inv).natTrans.app N ≫
        (StrictTower.towerDirectImage B f).map (aX.hom.app N) = d.hom.app N
    rw [D.mate]
    rfl
  rw [← hd]
  change HEq ((mateEquiv (VaryingRing.moduleAdj C τ f)
    (VaryingRing.scalarTowerAdj B f)).symm (TwoSquare.mk _ _ _ _ d.hom)).natTrans _
  rw [← hw, Equiv.symm_apply_apply]
  exact HEq.rfl

/-- Exact localization preserves the identified, conjugated pullback square. -/
private theorem normalized_pull_localized
    (D : VaryingRing.OrdinaryScalarComparison C τ B
      (fun n ↦ CommRingCat.ofHom (φ n)))
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (aX : D.rho X ≅ rhoOrdinary C τ B φ hφ X)
    (aY : D.rho Y ≅ rhoOrdinary C τ B φ hφ Y)
    (haX : ∀ (M : Modules C τ X) (n : ℕ) (H : X.ProEtᵒᵖ)
      (x : (((D.rho X).obj M).obj (op n)).val.obj H),
      HEq (((aX.hom.app M).app (op n)).val.app H x) x)
    (haY : ∀ (M : Modules C τ Y) (n : ℕ) (H : Y.ProEtᵒᵖ)
      (x : (((D.rho Y).obj M).obj (op n)).val.obj H),
      HEq (((aY.hom.app M).app (op n)).val.app H x) x)
    (F : Modules C τ X ⥤ Modules C τ Y) [F.IsRightAdjoint]
    [F.leftAdjoint.Additive] [PreservesFiniteLimits F.leftAdjoint]
    [PreservesFiniteColimits F.leftAdjoint]
    (hF : F = VaryingRing.push C τ f)
    (e : rhoOrdinary C τ B φ hφ X ⋙ StrictTower.towerDirectImage B f ≅
      F ⋙ rhoOrdinary C τ B φ hφ Y)
    (he : ∀ (M : Modules C τ X) (n : ℕ) (U : Y.ProEt),
      HEq (fun x ↦ ((e.hom.app M).app (op n)).val.app (op U) x)
        (fun x : M.val.obj (op (n, (Scheme.proEtaleBaseChange f).obj U)) ↦ x))
    (s : rhoOrdinary C τ B φ hφ Y ⋙ StrictTower.towerPullback B f ≅
      F.leftAdjoint ⋙ rhoOrdinary C τ B φ hφ X)
    (hs : s.hom = ((mateEquiv (Adjunction.ofIsRightAdjoint F)
      (VaryingRing.scalarTowerAdj B f)).symm (TwoSquare.mk _ _ _ _ e.inv)).natTrans) :
    HEq (localized_pull_iso C τ B φ hφ f F.leftAdjoint s).hom
      (Functor.whiskerRight (localized_scalar_iso C τ B φ hφ D Y aY).inv
          (StrictTower.G B f) ≫ (VaryingRing.scalarB D f).inv ≫
        Functor.whiskerLeft (VaryingRing.G C τ f)
          (localized_scalar_iso C τ B φ hφ D X aX).hom) := by
  subst F
  have h := normalized_pull C τ B φ hφ D f aX aY haX haY
    (VaryingRing.push C τ f) rfl e he
  let q : rhoOrdinary C τ B φ hφ Y ⋙ StrictTower.towerPullback B f ≅
      VaryingRing.pull C τ f ⋙ rhoOrdinary C τ B φ hφ X :=
    Functor.isoWhiskerRight aY.symm (StrictTower.towerPullback B f) ≪≫
      (D.b f).symm ≪≫ Functor.isoWhiskerLeft (VaryingRing.pull C τ f) aX
  have hq : s = q := by
    apply Iso.ext
    rw [hs]
    exact eq_of_heq h
  rw [hq]
  let rAX : (rhoOrdinary C τ B φ hφ X).Additive := rho_additive C τ B φ hφ X
  let rAY : (rhoOrdinary C τ B φ hφ Y).Additive := rho_additive C τ B φ hφ Y
  let rLX : PreservesFiniteLimits (rhoOrdinary C τ B φ hφ X) := rho_limits C τ B φ hφ X
  let rLY : PreservesFiniteLimits (rhoOrdinary C τ B φ hφ Y) := rho_limits C τ B φ hφ Y
  let rCX : PreservesFiniteColimits (rhoOrdinary C τ B φ hφ X) := rho_colimits C τ B φ hφ X
  let rCY : PreservesFiniteColimits (rhoOrdinary C τ B φ hφ Y) := rho_colimits C τ B φ hφ Y
  let dAX : (D.rho X).Additive := D.additive X
  let dAY : (D.rho Y).Additive := D.additive Y
  let dLX : PreservesFiniteLimits (D.rho X) := D.limits X
  let dLY : PreservesFiniteLimits (D.rho Y) := D.limits Y
  let dCX : PreservesFiniteColimits (D.rho X) := D.colimits X
  let dCY : PreservesFiniteColimits (D.rho Y) := D.colimits Y
  have ht := derived_square_conjugate aY.symm (D.b f).symm aX
  simp only [Functor.square_symm_hom, Functor.mapDerivedCategoryNatIso_symm] at ht
  exact ht.heq

/-- Identify the specified pullback comparison with the conjugated package comparison. -/
private theorem rhoP_conjugate
    (D : VaryingRing.OrdinaryScalarComparison C τ B
      (fun n ↦ CommRingCat.ofHom (φ n)))
    (a : ∀ X : Scheme.{u}, D.rho X ≅ rhoOrdinary C τ B φ hφ X)
    (ha : ∀ (X : Scheme.{u}) (M : Modules C τ X) (n : ℕ) (H : X.ProEtᵒᵖ)
      (x : (((D.rho X).obj M).obj (op n)).val.obj H),
      HEq ((((a X).hom.app M).app (op n)).val.app H x) x)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    HEq (rhoP C τ B φ hφ f).hom
      (Functor.whiskerLeft (VaryingRing.G C τ f)
          (localized_scalar_iso C τ B φ hφ D X (a X)).inv ≫
        (VaryingRing.scalarB D f).hom ≫
        Functor.whiskerRight (localized_scalar_iso C τ B φ hφ D Y (a Y)).hom
          (StrictTower.G B f)) := by
  have hn := normalized_pull_localized C τ B φ hφ D f (a X) (a Y) (ha X) (ha Y)
    (push C τ f) (push_eq C τ f)
    (rhoPushOrdinary_existsUnique C τ B φ hφ f).choose
    (rhoPushOrdinary_existsUnique C τ B φ hφ f).choose_spec.1
    (@asIso _ _ _ _ (rhoPullInv C τ B φ hφ f)
      (rhoPullInv_isIso C τ B φ hφ f)) rfl
  have he : (rhoP C τ B φ hφ f).inv =
      (localized_pull_iso C τ B φ hφ f (pull C τ f)
        (@asIso _ _ _ _ (rhoPullInv C τ B φ hφ f)
          (rhoPullInv_isIso C τ B φ hφ f))).hom := by
    let rAX : (rhoOrdinary C τ B φ hφ X).Additive := rho_additive C τ B φ hφ X
    let rAY : (rhoOrdinary C τ B φ hφ Y).Additive := rho_additive C τ B φ hφ Y
    let rLX : PreservesFiniteLimits (rhoOrdinary C τ B φ hφ X) := rho_limits C τ B φ hφ X
    let rLY : PreservesFiniteLimits (rhoOrdinary C τ B φ hφ Y) := rho_limits C τ B φ hφ Y
    let rCX : PreservesFiniteColimits (rhoOrdinary C τ B φ hφ X) := rho_colimits C τ B φ hφ X
    let rCY : PreservesFiniteColimits (rhoOrdinary C τ B φ hφ Y) := rho_colimits C τ B φ hφ Y
    unfold rhoP localized_pull_iso
    change
      ((Functor.mapDerivedCategoryCompIso (rhoOrdinary C τ B φ hφ Y)
          (StrictTower.towerPullback B f)).inv ≫
        (Functor.mapDerivedCategoryNatIso
          (@asIso _ _ _ _ (rhoPullInv C τ B φ hφ f)
            (rhoPullInv_isIso C τ B φ hφ f)).symm).inv) ≫
        (Functor.mapDerivedCategoryCompIso (pull C τ f)
          (rhoOrdinary C τ B φ hφ X)).hom =
      (Functor.mapDerivedCategoryCompIso (rhoOrdinary C τ B φ hφ Y)
          (StrictTower.towerPullback B f)).inv ≫
        (Functor.mapDerivedCategoryNatIso
          (@asIso _ _ _ _ (rhoPullInv C τ B φ hφ f)
            (rhoPullInv_isIso C τ B φ hφ f))).hom ≫
        (Functor.mapDerivedCategoryCompIso (pull C τ f)
          (rhoOrdinary C τ B φ hφ X)).hom
    rw [derived_iso_symm_inv]
    exact Category.assoc _ _ _
  let q := Functor.isoWhiskerLeft (VaryingRing.G C τ f)
      (localized_scalar_iso C τ B φ hφ D X (a X)).symm ≪≫
    VaryingRing.scalarB D f ≪≫
      Functor.isoWhiskerRight (localized_scalar_iso C τ B φ hφ D Y (a Y)) (StrictTower.G B f)
  have hi :
      Functor.whiskerRight (localized_scalar_iso C τ B φ hφ D Y (a Y)).inv
          (StrictTower.G B f) ≫ (VaryingRing.scalarB D f).inv ≫
        Functor.whiskerLeft (VaryingRing.G C τ f)
          (localized_scalar_iso C τ B φ hφ D X (a X)).hom = q.inv := by
    exact (Category.assoc _ _ _).symm
  exact iso_hom_of_inv_heq (rhoP C τ B φ hφ f) q
    (congrArg (fun F ↦ F ⋙ rho C τ B φ hφ X) (P_eq C τ f)) rfl
    (he.heq.trans (hn.trans hi.heq))

include hφ in
private theorem scalarA_inverse_mate
    (D : VaryingRing.OrdinaryScalarComparison C τ B
      (fun n ↦ CommRingCat.ofHom (φ n))) {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    ((mateEquiv (VaryingRing.jAdj C τ j) (StrictTower.jAdj B j)).symm
      (TwoSquare.mk _ _ _ _ (VaryingRing.scalarB D j).hom)).natTrans =
      (VaryingRing.scalarA D j).inv := by
  apply NatTrans.ext
  funext M
  rw [inverse_mate_app, Adjunction.homEquiv_counit]
  have hψ : ∀ n, CommRingCat.ofHom (φ (n + 1)) ≫ τ n = CommRingCat.ofHom (φ n) :=
    fun n ↦ CommRingCat.hom_ext (hφ n)
  simpa only [Functor.map_comp, Category.assoc] using
    ((VaryingRing.derivedScalarComparison D hψ).2.1 j M).symm

/-- Identify the specified open comparison by transposing the pullback comparison. -/
private theorem rhoJ_conjugate
    (D : VaryingRing.OrdinaryScalarComparison C τ B
      (fun n ↦ CommRingCat.ofHom (φ n)))
    (a : ∀ X : Scheme.{u}, D.rho X ≅ rhoOrdinary C τ B φ hφ X)
    (ha : ∀ (X : Scheme.{u}) (M : Modules C τ X) (n : ℕ) (H : X.ProEtᵒᵖ)
      (x : (((D.rho X).obj M).obj (op n)).val.obj H),
      HEq ((((a X).hom.app M).app (op n)).val.app H x) x)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    HEq (rhoJ C τ B φ hφ j).hom
      (Functor.whiskerLeft (VaryingRing.J C τ j)
          (localized_scalar_iso C τ B φ hφ D X (a X)).inv ≫
        (VaryingRing.scalarA D j).hom ≫
        Functor.whiskerRight (localized_scalar_iso C τ B φ hφ D U (a U)).hom
          (StrictTower.J B j)) := by
  let AU := localized_scalar_iso C τ B φ hφ D U (a U)
  let AX := localized_scalar_iso C τ B φ hφ D X (a X)
  let b := Functor.whiskerLeft (VaryingRing.G C τ j) AU.inv ≫
    (VaryingRing.scalarB D j).hom ≫ Functor.whiskerRight AX.hom (StrictTower.G B j)
  have hm := inverse_mate_heq
    (jAdj C τ j) (VaryingRing.jAdj C τ j)
    (StrictTower.jAdj B j) (StrictTower.jAdj B j)
    (rhoP C τ B φ hφ j).hom b (J_eq C τ j) (P_eq C τ j) rfl rfl rfl rfl
    (Normalization.jadj_heq C τ j) HEq.rfl (rhoP_conjugate C τ B φ hφ D a ha j)
  let w := ((TwoSquare.mk _ _ _ _ (VaryingRing.scalarA D j).inv).whiskerTop
    AU.inv).whiskerBottom AX.hom
  have hw : mateEquiv (VaryingRing.jAdj C τ j) (StrictTower.jAdj B j) w =
      TwoSquare.mk _ _ _ _ b := by
    dsimp only [w]
    rw [mateEquiv_whiskerTop_whiskerBottom]
    have hs : mateEquiv (VaryingRing.jAdj C τ j) (StrictTower.jAdj B j)
        (TwoSquare.mk _ _ _ _ (VaryingRing.scalarA D j).inv) =
        TwoSquare.mk _ _ _ _ (VaryingRing.scalarB D j).hom := by
      exact (Equiv.eq_symm_apply _).mp (scalarA_inverse_mate C τ B φ hφ D j).symm
    rw [hs]
    apply TwoSquare.ext
    intro N
    exact Category.assoc _ _ _
  rw [← hw, Equiv.symm_apply_apply] at hm
  let q := Functor.isoWhiskerLeft (VaryingRing.J C τ j) AX.symm ≪≫
    VaryingRing.scalarA D j ≪≫ Functor.isoWhiskerRight AU (StrictTower.J B j)
  exact iso_hom_of_inv_heq (rhoJ C τ B φ hφ j) q
    (congrArg (fun F ↦ F ⋙ rho C τ B φ hφ X) (J_eq C τ j)) rfl hm

attribute [local irreducible] rhoP rhoJ VaryingRing.scalarB VaryingRing.scalarA

include hφ in
private theorem scalar_alpha_component
    (D : VaryingRing.OrdinaryScalarComparison C τ B
      (fun n ↦ CommRingCat.ofHom (φ n)))
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (M : Derived C τ S) :
    (VaryingRing.scalarRho D W).map ((VaryingRing.alpha C τ k r p i h).app M) ≫
        (VaryingRing.scalarA D k).hom.app ((VaryingRing.G C τ r).obj M) ≫
        (StrictTower.J B k).map ((VaryingRing.scalarB D r).hom.app M) =
      (VaryingRing.scalarB D p).hom.app ((VaryingRing.J C τ i).obj M) ≫
        (StrictTower.G B p).map ((VaryingRing.scalarA D i).hom.app M) ≫
        (StrictTower.alpha B k r p i h).app ((VaryingRing.scalarRho D S).obj M) := by
  have hψ : ∀ n, CommRingCat.ofHom (φ (n + 1)) ≫ τ n = CommRingCat.ofHom (φ n) :=
    fun n ↦ CommRingCat.hom_ext (hφ n)
  exact (VaryingRing.derivedScalarComparison D hψ).2.2 k r p i h M

private def native_rho (X : Scheme.{u}) :
    VaryingRing.Derived C τ X ⥤ StrictTower.Derived B X where
  obj M := (rho C τ B φ hφ X).obj M
  map f := (rho C τ B φ hφ X).map f
  map_id M := (rho C τ B φ hφ X).map_id M
  map_comp f g := (rho C τ B φ hφ X).map_comp f g

private def native_iso
    (D : VaryingRing.OrdinaryScalarComparison C τ B
      (fun n ↦ CommRingCat.ofHom (φ n)))
    (A : ∀ X : Scheme.{u}, VaryingRing.scalarRho D X ≅ rho C τ B φ hφ X)
    (X : Scheme.{u}) : VaryingRing.scalarRho D X ≅ native_rho C τ B φ hφ X where
  hom := { app := (A X).hom.app, naturality := (A X).hom.naturality }
  inv := { app := (A X).inv.app, naturality := (A X).inv.naturality }
  hom_inv_id := by ext M; exact (A X).hom_inv_id_app M
  inv_hom_id := by ext M; exact (A X).inv_hom_id_app M

/-- Conjugate the scalar alpha equation by cancellation of its boundary isomorphisms. -/
private theorem normalized_alpha_native
    (D : VaryingRing.OrdinaryScalarComparison C τ B
      (fun n ↦ CommRingCat.ofHom (φ n)))
    (A : ∀ X : Scheme.{u}, VaryingRing.scalarRho D X ≅ native_rho C τ B φ hφ X)
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (M : VaryingRing.Derived C τ S) :
    let qi := Functor.isoWhiskerLeft (VaryingRing.J C τ i) (A T).symm ≪≫
      VaryingRing.scalarA D i ≪≫ Functor.isoWhiskerRight (A S) (StrictTower.J B i)
    let qk := Functor.isoWhiskerLeft (VaryingRing.J C τ k) (A W).symm ≪≫
      VaryingRing.scalarA D k ≪≫ Functor.isoWhiskerRight (A V) (StrictTower.J B k)
    let qp := Functor.isoWhiskerLeft (VaryingRing.G C τ p) (A W).symm ≪≫
      VaryingRing.scalarB D p ≪≫ Functor.isoWhiskerRight (A T) (StrictTower.G B p)
    let qr := Functor.isoWhiskerLeft (VaryingRing.G C τ r) (A V).symm ≪≫
      VaryingRing.scalarB D r ≪≫ Functor.isoWhiskerRight (A S) (StrictTower.G B r)
    (native_rho C τ B φ hφ W).map ((VaryingRing.alpha C τ k r p i h).app M) ≫
        qk.hom.app ((VaryingRing.G C τ r).obj M) ≫
        (StrictTower.J B k).map (qr.hom.app M) =
      qp.hom.app ((VaryingRing.J C τ i).obj M) ≫
        (StrictTower.G B p).map (qi.hom.app M) ≫
        (StrictTower.alpha B k r p i h).app ((native_rho C τ B φ hφ S).obj M) := by
  dsimp only
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  apply (cancel_epi ((A W).hom.app
    ((VaryingRing.G C τ p).obj ((VaryingRing.J C τ i).obj M)))).mp
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← (A W).hom.naturality_assoc]
  simp only [Functor.comp_obj, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (scalar_alpha_component C τ B φ hφ D k r p i h M)]
  have hn := (StrictTower.alpha B k r p i h).naturality ((A S).hom.app M)
  dsimp only [Functor.comp_map] at hn
  rw [← hn]

attribute [local irreducible] P J StrictTower.G StrictTower.J
  StrictTower.alpha VaryingRing.alpha localized_scalar_iso

private theorem app_heq
    {A B : Type*} [Category A] [Category B]
    {F F' G G' : A ⥤ B} (a : F ⟶ G) (b : F' ⟶ G')
    (hF : F = F') (hG : G = G') (hab : HEq a b) {M N : A} (hM : M = N) :
    HEq (a.app M) (b.app N) := by
  subst F' G' N
  cases hab
  rfl

private theorem map_heq
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {M M' N N' : A} (f : M ⟶ N) (g : M' ⟶ N')
    (hM : M = M') (hN : N = N') (hfg : HEq f g) : HEq (F.map f) (F.map g) := by
  subst M' N'
  cases hfg
  rfl

private theorem composition_heq
    {C : Type*} [Category C] {A A' B B' D D' : C}
    (f : A ⟶ B) (f' : A' ⟶ B') (g : B ⟶ D) (g' : B' ⟶ D')
    (hA : A = A') (hB : B = B') (hD : D = D') (hf : HEq f f') (hg : HEq g g') :
    HEq (f ≫ g) (f' ≫ g') := by
  subst A' B' D'
  cases hf
  cases hg
  rfl

/-- The copied functor retains the chosen object map. -/
private theorem native_rho_obj (X : Scheme.{u}) (M : VaryingRing.Derived C τ X) :
    (native_rho C τ B φ hφ X).obj M = (rho C τ B φ hφ X).obj M := rfl

/-- The copied morphism map is heterogeneously the chosen morphism map. -/
private theorem native_rho_map_heq (X : Scheme.{u}) {M N : VaryingRing.Derived C τ X}
    (f : M ⟶ N) :
    HEq ((native_rho C τ B φ hφ X).map f) ((rho C τ B φ hφ X).map f) := HEq.rfl

/-- Copying the scalar identification retains the conjugated open component. -/
private theorem native_open_projection
    (D : VaryingRing.OrdinaryScalarComparison C τ B
      (fun n ↦ CommRingCat.ofHom (φ n)))
    (A : ∀ X : Scheme.{u}, VaryingRing.scalarRho D X ≅ rho C τ B φ hφ X)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : VaryingRing.Derived C τ U) :
    HEq ((Functor.isoWhiskerLeft (VaryingRing.J C τ j)
          (native_iso C τ B φ hφ D A X).symm ≪≫ VaryingRing.scalarA D j ≪≫
        Functor.isoWhiskerRight (native_iso C τ B φ hφ D A U)
          (StrictTower.J B j)).hom.app M)
      ((Functor.whiskerLeft (VaryingRing.J C τ j) (A X).inv ≫
          (VaryingRing.scalarA D j).hom ≫
          Functor.whiskerRight (A U).hom (StrictTower.J B j)).app M) := by
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    native_iso, native_rho]
  rfl

/-- Copying the scalar identification retains the conjugated pullback component. -/
private theorem native_pull_projection
    (D : VaryingRing.OrdinaryScalarComparison C τ B
      (fun n ↦ CommRingCat.ofHom (φ n)))
    (A : ∀ X : Scheme.{u}, VaryingRing.scalarRho D X ≅ rho C τ B φ hφ X)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : VaryingRing.Derived C τ Y) :
    HEq ((Functor.isoWhiskerLeft (VaryingRing.G C τ f)
          (native_iso C τ B φ hφ D A X).symm ≪≫ VaryingRing.scalarB D f ≪≫
        Functor.isoWhiskerRight (native_iso C τ B φ hφ D A Y)
          (StrictTower.G B f)).hom.app M)
      ((Functor.whiskerLeft (VaryingRing.G C τ f) (A X).inv ≫
          (VaryingRing.scalarB D f).hom ≫
          Functor.whiskerRight (A Y).hom (StrictTower.G B f)).app M) := by
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    native_iso, native_rho]
  rfl

attribute [local irreducible] native_rho native_iso

private theorem normalized_alpha_word
    (D : VaryingRing.OrdinaryScalarComparison C τ B
      (fun n ↦ CommRingCat.ofHom (φ n)))
    (A : ∀ X : Scheme.{u}, VaryingRing.scalarRho D X ≅ rho C τ B φ hφ X)
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (M : Derived C τ S) :
    let qi := Functor.whiskerLeft (VaryingRing.J C τ i) (A T).inv ≫
      (VaryingRing.scalarA D i).hom ≫
        Functor.whiskerRight (A S).hom (StrictTower.J B i)
    let qk := Functor.whiskerLeft (VaryingRing.J C τ k) (A W).inv ≫
      (VaryingRing.scalarA D k).hom ≫
        Functor.whiskerRight (A V).hom (StrictTower.J B k)
    let qp := Functor.whiskerLeft (VaryingRing.G C τ p) (A W).inv ≫
      (VaryingRing.scalarB D p).hom ≫
        Functor.whiskerRight (A T).hom (StrictTower.G B p)
    let qr := Functor.whiskerLeft (VaryingRing.G C τ r) (A V).inv ≫
      (VaryingRing.scalarB D r).hom ≫
        Functor.whiskerRight (A S).hom (StrictTower.G B r)
    (rho C τ B φ hφ W).map ((VaryingRing.alpha C τ k r p i h).app M) ≫
        qk.app ((VaryingRing.G C τ r).obj M) ≫
        (StrictTower.J B k).map (qr.app M) =
      qp.app ((VaryingRing.J C τ i).obj M) ≫
        (StrictTower.G B p).map (qi.app M) ≫
        (StrictTower.alpha B k r p i h).app ((rho C τ B φ hφ S).obj M) := by
  let A' := fun X ↦ native_iso C τ B φ hφ D A X
  have hc := normalized_alpha_native C τ B φ hφ D A' k r p i h M
  dsimp only at hc ⊢
  have eS := native_rho_obj C τ B φ hφ S M
  have eT := native_rho_obj C τ B φ hφ T ((VaryingRing.J C τ i).obj M)
  have eV := native_rho_obj C τ B φ hφ V ((VaryingRing.G C τ r).obj M)
  have eW₀ := native_rho_obj C τ B φ hφ W
    ((VaryingRing.G C τ p).obj ((VaryingRing.J C τ i).obj M))
  have eW₁ := native_rho_obj C τ B φ hφ W
    ((VaryingRing.J C τ k).obj ((VaryingRing.G C τ r).obj M))
  have eJV := congrArg (StrictTower.J B k).obj eV
  have eGT := congrArg (StrictTower.G B p).obj eT
  have eGI := congrArg
    (fun N ↦ (StrictTower.G B p).obj ((StrictTower.J B i).obj N)) eS
  have eJG := congrArg
    (fun N ↦ (StrictTower.J B k).obj ((StrictTower.G B r).obj N)) eS
  have h1 := native_rho_map_heq C τ B φ hφ W
    ((VaryingRing.alpha C τ k r p i h).app M)
  have h2 := native_open_projection C τ B φ hφ D A k
    ((VaryingRing.G C τ r).obj M)
  have h3a := native_pull_projection C τ B φ hφ D A r M
  have h3 := map_heq (StrictTower.J B k) _ _ eV
    (congrArg (StrictTower.G B r).obj eS) h3a
  have h4 := native_pull_projection C τ B φ hφ D A p
    ((VaryingRing.J C τ i).obj M)
  have h5a := native_open_projection C τ B φ hφ D A i M
  have h5 := map_heq (StrictTower.G B p) _ _ eT
    (congrArg (StrictTower.J B i).obj eS) h5a
  have h6 := app_heq (StrictTower.alpha B k r p i h)
    (StrictTower.alpha B k r p i h) rfl rfl HEq.rfl eS
  have h23 := composition_heq (C := StrictTower.Derived B W) _ _ _ _
    eW₁ eJV eJG h2 h3
  have hL := composition_heq (C := StrictTower.Derived B W) _ _ _ _
    eW₀ eW₁ eJG h1 h23
  have h56 := composition_heq (C := StrictTower.Derived B W) _ _ _ _
    eGT eGI eJG h5 h6
  have hR := composition_heq (C := StrictTower.Derived B W) _ _ _ _
    eW₀ eGT eJG h4 h56
  exact eq_of_heq (hL.symm.trans (hc.heq.trans hR))

private theorem specialized_transfer
    (D : VaryingRing.OrdinaryScalarComparison C τ B
      (fun n ↦ CommRingCat.ofHom (φ n)))
    (a : ∀ X : Scheme.{u}, D.rho X ≅ rhoOrdinary C τ B φ hφ X)
    (ha : ∀ (X : Scheme.{u}) (M : Modules C τ X) (n : ℕ) (H : X.ProEtᵒᵖ)
      (x : (((D.rho X).obj M).obj (op n)).val.obj H),
      HEq ((((a X).hom.app M).app (op n)).val.app H x) x)
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (M : Derived C τ S) :
    (rho C τ B φ hφ W).map ((alpha C τ k r p i h).app M) ≫
        (rhoJ C τ B φ hφ k).hom.app ((P C τ r).obj M) ≫
        (StrictTower.J B k).map ((rhoP C τ B φ hφ r).hom.app M) =
      (rhoP C τ B φ hφ p).hom.app ((J C τ i).obj M) ≫
        (StrictTower.G B p).map ((rhoJ C τ B φ hφ i).hom.app M) ≫
        (StrictTower.alpha B k r p i h).app ((rho C τ B φ hφ S).obj M) := by
  let A := fun X ↦ localized_scalar_iso C τ B φ hφ D X (a X)
  let qi := Functor.whiskerLeft (VaryingRing.J C τ i) (A T).inv ≫
    (VaryingRing.scalarA D i).hom ≫ Functor.whiskerRight (A S).hom (StrictTower.J B i)
  let qk := Functor.whiskerLeft (VaryingRing.J C τ k) (A W).inv ≫
    (VaryingRing.scalarA D k).hom ≫ Functor.whiskerRight (A V).hom (StrictTower.J B k)
  let qp := Functor.whiskerLeft (VaryingRing.G C τ p) (A W).inv ≫
    (VaryingRing.scalarB D p).hom ≫ Functor.whiskerRight (A T).hom (StrictTower.G B p)
  let qr := Functor.whiskerLeft (VaryingRing.G C τ r) (A V).inv ≫
    (VaryingRing.scalarB D r).hom ≫ Functor.whiskerRight (A S).hom (StrictTower.G B r)
  have hα : HEq (alpha C τ k r p i h) (VaryingRing.alpha C τ k r p i h) := by
    unfold VaryingRing.alpha
    exact (Normalization.system_alpha_localized C τ k r p i h).symm
  have hc := normalized_alpha_word C τ B φ hφ D A k r p i h M
  have hαM := app_heq (alpha C τ k r p i h) (VaryingRing.alpha C τ k r p i h)
    (by rw [J_eq C τ i, P_eq C τ p])
    (by rw [P_eq C τ r, J_eq C τ k]) hα (rfl : M = M)
  have h1 := map_heq (rho C τ B φ hφ W) _ _
    (by rw [J_eq C τ i, P_eq C τ p])
    (by rw [P_eq C τ r, J_eq C τ k]) hαM
  have h2 := app_heq (rhoJ C τ B φ hφ k).hom qk
    (by rw [J_eq C τ k]) rfl (rhoJ_conjugate C τ B φ hφ D a ha k)
    (congrArg (fun F ↦ F.obj M) (P_eq C τ r))
  have h3a := app_heq (rhoP C τ B φ hφ r).hom qr
    (by rw [P_eq C τ r]) rfl (rhoP_conjugate C τ B φ hφ D a ha r) (rfl : M = M)
  have h3 := map_heq (StrictTower.J B k) _ _ (by rw [P_eq C τ r]) rfl h3a
  have h4 := app_heq (rhoP C τ B φ hφ p).hom qp
    (by rw [P_eq C τ p]) rfl (rhoP_conjugate C τ B φ hφ D a ha p)
    (congrArg (fun F ↦ F.obj M) (J_eq C τ i))
  have h5a := app_heq (rhoJ C τ B φ hφ i).hom qi
    (by rw [J_eq C τ i]) rfl (rhoJ_conjugate C τ B φ hφ D a ha i) (rfl : M = M)
  have h5 := map_heq (StrictTower.G B p) _ _ (by rw [J_eq C τ i]) rfl h5a
  have h23 := composition_heq (C := StrictTower.Derived B W) _ _ _ _
    (by rw [P_eq C τ r, J_eq C τ k]) (by rw [P_eq C τ r]) rfl h2 h3
  have hL := composition_heq (C := StrictTower.Derived B W) _ _ _ _
    (by rw [J_eq C τ i, P_eq C τ p])
    (by rw [P_eq C τ r, J_eq C τ k]) rfl h1 h23
  have h5f := composition_heq (C := StrictTower.Derived B W) _ _
    ((StrictTower.alpha B k r p i h).app ((rho C τ B φ hφ S).obj M))
    ((StrictTower.alpha B k r p i h).app ((rho C τ B φ hφ S).obj M))
    (by rw [J_eq C τ i]) rfl rfl h5 HEq.rfl
  have hR := composition_heq (C := StrictTower.Derived B W) _ _ _ _
    (by rw [J_eq C τ i, P_eq C τ p]) (by rw [J_eq C τ i]) rfl h4 h5f
  exact eq_of_heq (hL.trans (hc.heq.trans hR.symm))


/-- Scalar preserves the specified inverse-image alpha word, before taking proper mates.
Source: Stacks Project, Tags 03DI and 0F7B; Zheng, Construction 4.1 and Lemma 4.10.
Proof: obtain the ordinary scalar comparison package D. Its level identifications
and transition equations give a section-normalized isomorphism from D.rho to the
chosen rhoOrdinary. Conjugating D.d by these isomorphisms gives the chosen ordinary
direct-image comparison: both are identity on every section. Transpose this identity
and localize it to identify scalarB D with the conjugate of rhoP. Transpose again
under the open adjunction to identify scalarA D with the conjugate of rhoJ; the
open units fix this identification uniquely. Apply the alpha preservation clause
of derivedScalarComparison, and the pre-mate alpha normalization from the intrinsic/
varying-ring comparison. Substitute these conjugation formulas. Naturality moves
the boundary identifications past alpha and its strict-tower counterpart, and the
inverse pairs cancel. This proves the stated equation on whole derived systems.
The clopen projection used by the ordinary package is (1,0), so empty components,
zero coefficient rings and nonflat coefficient maps require no extra hypothesis.
No proper-adjunction mate of alpha is taken in this argument.
(blueprint: lem-sf-intrinsic-scalar-alpha-compatibility). -/
theorem intrinsicScalarAlphaCompatibility
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (M : Derived C τ S) :
    (rho C τ B φ hφ W).map ((alpha C τ k r p i h).app M) ≫
        (rhoJ C τ B φ hφ k).hom.app ((P C τ r).obj M) ≫
        (StrictTower.J B k).map ((rhoP C τ B φ hφ r).hom.app M) =
      (rhoP C τ B φ hφ p).hom.app ((J C τ i).obj M) ≫
        (StrictTower.G B p).map ((rhoJ C τ B φ hφ i).hom.app M) ≫
        (StrictTower.alpha B k r p i h).app ((rho C τ B φ hφ S).obj M) := by
  have hψ : ∀ n, CommRingCat.ofHom (φ (n + 1)) ≫ τ n = CommRingCat.ofHom (φ n) :=
    fun n ↦ CommRingCat.hom_ext (hφ n)
  obtain ⟨D⟩ := VaryingRing.ordinaryScalarComparison C τ B
    (fun n ↦ CommRingCat.ofHom (φ n)) hψ
  let E : VaryingRing.OrdinaryScalarRestriction C τ B
      (fun n ↦ CommRingCat.ofHom (φ n)) :=
    { rho := D.rho
      additive := D.additive
      limits := D.limits
      colimits := D.colimits
      level := D.level
      level_sections := D.level_sections
      transitions := D.transitions }
  choose a ha using fun X ↦ restriction_rho_iso C τ B φ hφ E X
  exact specialized_transfer C τ B φ hφ D a ha k r p i h M

end NormalizedComparison

end AlgebraicGeometry.ProEtale.SemilinearProperOpen
