/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.Paper.AdicFiniteReductionData
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence

/-! # Explicit transport of inverse-image constant coefficients to the small site -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Inverse image preserves the constant coefficient ring by uniqueness of left adjoints.
Source: Stacks Tag 0H7J
(blueprint: lem-weil-pbc-relative-finite-coefficient-transport). -/
theorem relativeFiniteConstantInverseImage_isIso {X Y : Scheme.{u}} (g : Y ⟶ X)
    (B : Type (u + 1)) [CommRing B] :
    IsIso (proEtaleConstantInverseImageMap g CommRingCat.{u + 1} (CommRingCat.of B)) := by
  let G := proEtaleBaseChange g
  let hX : IsTerminal (⊤_ X.ProEt) := terminalIsTerminal
  let hY := hX.isTerminalObj G _
  let aX := constantSheafAdj (ProEt.topology X) CommRingCat.{u + 1} hX
  let adj := proEtaleSheafAdjunction g CommRingCat.{u + 1}
  let a := (aX.comp adj).ofNatIsoRight (Iso.refl _)
  let b := constantSheafAdj (ProEt.topology Y) CommRingCat.{u + 1} hY
  let e := a.leftAdjointUniq b
  have he : proEtaleConstantInverseImageMap g CommRingCat.{u + 1}
      (CommRingCat.of B) = e.hom.app (CommRingCat.of B) := by
    apply (a.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    simp only [a, Adjunction.homEquiv_ofNatIsoRight_apply, Iso.refl_hom,
      NatTrans.id_app, Category.comp_id, Adjunction.comp_homEquiv]
    dsimp [proEtaleConstantInverseImageMap]
    rw [← Adjunction.homEquiv_counit]
    dsimp only [adj]
    rw [Equiv.apply_symm_apply]
    dsimp only [proEtaleConstantDirectImageMap, aX, constantSheafAdj]
    rw [Adjunction.comp_homEquiv]
    change (constantPresheafAdj CommRingCat.{u + 1} hX).homEquiv _ _
      (((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
        _ _)
        (((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
          _ _).symm _)) = _
    rw [Equiv.apply_symm_apply]
    rfl
  rw [he]
  infer_instance

/-- The canonical coefficient identification, first along the equivalence of sites,
then along inverse image. Both comparisons are constructed by their adjunctions.
Source: Stacks Tags 00VC, 03A0, and 0H7J
(blueprint: lem-weil-pbc-relative-finite-coefficient-transport). -/
def relativeFiniteModelCoefficient {X Y : Scheme.{u}} (g : Y ⟶ X)
    (B : Type (u + 1)) [CommRing B] :
    CategoryTheory.ConstantCompletion.constant (proEtaleModelTopology Y) B ≅
      ((AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).sheafPushforwardContinuous
        CommRingCat.{u + 1} (proEtaleModelTopology Y) (ProEt.topology Y)).obj
          ((adicTowerInverseImage g).obj (adicLisseConstantRing X B)) := by
  let e := AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)
  have : (AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).IsEquivalence :=
    e.isEquivalence_inverse
  have : e.inverse.IsDenseSubsite (proEtaleModelTopology Y) (ProEt.topology Y) := by
    change AsSmall.down.IsDenseSubsite (AsSmall.down.inducedTopology (ProEt.topology Y)) _
    infer_instance
  have := relativeFiniteConstantInverseImage_isIso g B
  exact ((e.constantSheafSheafCongrIso (ProEt.topology Y) (proEtaleModelTopology Y)
    CommRingCat.{u + 1} terminalIsTerminal).app (CommRingCat.of B)).symm ≪≫
      ((AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).sheafPushforwardContinuous
        CommRingCat.{u + 1} (proEtaleModelTopology Y) (ProEt.topology Y)).mapIso
          (asIso (proEtaleConstantInverseImageMap g CommRingCat.{u + 1}
            (CommRingCat.of B))).symm

/-- Sectionwise transport with scalar action through the canonical coefficient map.
There is no choice of module objects in this definition.
Source: Stacks Tags 03A0 and 03D1
(blueprint: lem-weil-pbc-relative-finite-coefficient-transport). -/
def relativeFiniteModelModules {X Y : Scheme.{u}} (g : Y ⟶ X)
    (B : Type (u + 1)) [CommRing B] :
    pbcModules Y ((adicTowerInverseImage g).obj (adicLisseConstantRing X B)) ⥤
      CategoryTheory.ConstantCompletion.Mod
        (CategoryTheory.ConstantCompletion.constant (proEtaleModelTopology Y) B) :=
  proEtaleModuleToModel ((adicLisseForget Y).obj
      ((adicTowerInverseImage g).obj (adicLisseConstantRing X B))) ⋙
    SheafOfModules.restrictScalars
      ((sheafCompose (proEtaleModelTopology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (relativeFiniteModelCoefficient g B).hom)

private theorem toModel_isEquivalence (Y : Scheme.{u})
    (R : Sheaf (ProEt.topology Y) RingCat.{u + 1}) :
    (proEtaleModuleToModel R).IsEquivalence := by
  let S := ((AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).sheafPushforwardContinuous
    RingCat.{u + 1} (proEtaleModelTopology Y) (ProEt.topology Y)).obj R
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).functor.IsContinuous
      (ProEt.topology Y) (proEtaleModelTopology Y) := proEtaleModelUp_isContinuous Y
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).inverse.IsContinuous
      (proEtaleModelTopology Y) (ProEt.topology Y) := by
    change AsSmall.down.IsContinuous (proEtaleModelTopology Y) (ProEt.topology Y)
    infer_instance
  let e := SheafOfModules.pushforwardPushforwardEquivalence
    (AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)) (𝟙 R) (𝟙 S)
    (by ext V; dsimp [AsSmall.equiv]; erw [S.obj.map_id]; rfl)
    (by ext V; dsimp [AsSmall.equiv]; erw [R.obj.map_id]; rfl)
  exact inferInstanceAs e.inverse.IsEquivalence

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem isoRestriction_isEquivalence
    {C : Type (u + 1)} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) :
    (SheafOfModules.restrictScalars.{u + 1} c.hom).IsEquivalence := by
  let ec : C ≌ C := CategoryTheory.Equivalence.refl
  have : ec.functor.IsContinuous J J :=
    inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  have : ec.inverse.IsContinuous J J :=
    inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  let e := SheafOfModules.pushforwardPushforwardEquivalence (J := J) (K := J)
    ec c.hom c.inv
    (by
      ext V x
      dsimp [ec, CategoryTheory.Equivalence.refl]
      simpa only [S.obj.map_id, ObjectProperty.FullSubcategory.id_hom,
        ObjectProperty.FullSubcategory.comp_hom, NatTrans.id_app, NatTrans.comp_app,
        RingCat.hom_id, RingCat.hom_comp, RingHom.comp_apply, RingHom.id_apply] using
        congrArg (fun f : S ⟶ S ↦ (f.hom.app V).hom x) c.inv_hom_id.symm)
    (by
      ext V x
      dsimp [ec, CategoryTheory.Equivalence.refl]
      simpa only [R.obj.map_id, ObjectProperty.FullSubcategory.id_hom,
        ObjectProperty.FullSubcategory.comp_hom, NatTrans.id_app, NatTrans.comp_app,
        RingCat.hom_id, RingCat.hom_comp, RingHom.comp_apply, RingHom.id_apply] using
        congrArg (fun f : R ⟶ R ↦ (f.hom.app V).hom x) c.hom_inv_id)
  exact inferInstanceAs e.functor.IsEquivalence

/-- The explicit coefficient transport is an equivalence of module categories.
Source: Stacks Tags 03A0 and 03D1
(blueprint: lem-weil-pbc-relative-finite-coefficient-transport). -/
instance relativeFiniteModelModules_isEquivalence {X Y : Scheme.{u}} (g : Y ⟶ X)
    (B : Type (u + 1)) [CommRing B] :
    (relativeFiniteModelModules g B).IsEquivalence := by
  have := toModel_isEquivalence Y ((adicLisseForget Y).obj
    ((adicTowerInverseImage g).obj (adicLisseConstantRing X B)))
  have : (SheafOfModules.restrictScalars
      ((sheafCompose (proEtaleModelTopology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (relativeFiniteModelCoefficient g B).hom)).IsEquivalence :=
    isoRestriction_isEquivalence
    ((sheafCompose (proEtaleModelTopology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
        (relativeFiniteModelCoefficient g B))
  unfold relativeFiniteModelModules
  infer_instance

/-- The transport preserves addition on maps, section by section.
Source: Stacks Tag 03D1
(blueprint: lem-weil-pbc-relative-finite-coefficient-transport). -/
instance relativeFiniteModelModules_additive {X Y : Scheme.{u}} (g : Y ⟶ X)
    (B : Type (u + 1)) [CommRing B] : (relativeFiniteModelModules g B).Additive where
  map_add := by intros; rfl

attribute [-instance] WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientRingSheafify in
/-- The exact transport on the standard derived localizations.
Source: Stacks Tags 03D1 and 05RU
(blueprint: lem-weil-pbc-relative-finite-coefficient-transport). -/
def relativeFiniteModelDerived {X Y : Scheme.{u}} (g : Y ⟶ X)
    (B : Type (u + 1)) [CommRing B] :
    DerivedCategory (pbcModules Y
      ((adicTowerInverseImage g).obj (adicLisseConstantRing X B))) ⥤
      CategoryTheory.ConstantCompletion.D
        (CategoryTheory.ConstantCompletion.constant (proEtaleModelTopology Y) B) := by
  let := HasDerivedCategory.standard (CategoryTheory.ConstantCompletion.Mod
    (CategoryTheory.ConstantCompletion.constant (proEtaleModelTopology Y) B))
  exact (relativeFiniteModelModules g B).mapDerivedCategory

attribute [-instance] WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientRingSheafify in
/-- Exact transport commutes with homology in every degree.
Source: Stacks Tag 03D1
(blueprint: lem-weil-pbc-relative-finite-coefficient-transport). -/
def relativeFiniteModelHomologyIso {X Y : Scheme.{u}} (g : Y ⟶ X)
    (B : Type (u + 1)) [CommRing B]
    (K : DerivedCategory (pbcModules Y
      ((adicTowerInverseImage g).obj (adicLisseConstantRing X B)))) (q : ℤ) :
    (relativeFiniteModelModules g B).obj ((DerivedCategory.homologyFunctor _ q).obj K) ≅
      (coefficientModelCohomology _ q).obj ((relativeFiniteModelDerived g B).obj K) := by
  let := HasDerivedCategory.standard (CategoryTheory.ConstantCompletion.Mod
    (CategoryTheory.ConstantCompletion.constant (proEtaleModelTopology Y) B))
  exact ((relativeFiniteModelModules g B).mapDerivedCategoryHomologyFunctorIso q).app K

end AlgebraicGeometry.Scheme
