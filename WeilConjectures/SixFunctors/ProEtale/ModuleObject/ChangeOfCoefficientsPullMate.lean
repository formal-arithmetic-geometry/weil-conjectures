/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-!

# The underived (Pull) is a mate

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings and `f : X ⟶ Y` a morphism of
schemes. The underived (Pull) `ProEtale.CondensedRing.pullIso a f : f^*_Λ ⋙ Ext_{a_X} ≅
Ext_{a_Y} ⋙ f^*_Λ'` is defined as the conjugate of the commutation `comapLowerStarIso` of the
restriction of scalars with the pushforwards. This file shows that it is also the mate, under the
extension-restriction adjunctions, of the inverse of the commutation `comapUpperStarIso` of the
restriction of scalars with the pullbacks (`ProEtale.CondensedRing.mateEquiv_pullIso_hom`), i.e.
that (Pull) is compatible with the units of `Ext ⊣ Res`
(`ProEtale.CondensedRing.upperStar_map_unit_comp_comapUpperStarIso_inv_app`).

The key input is that `comapUpperStarIso` and `comapLowerStarIso` are mates under `f^* ⊣ f_*`
(`ProEtale.CondensedRing.mateEquiv_comapUpperStarIso_inv`), which is checked on underlying
sheaves; the statement then follows from the iterated mate correspondence
`iterated_mateEquiv_conjugateEquiv`.

-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  [BraidedCategory C] [MonoidalClosed C] [HasEqualizers C]

section

variable {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]

omit [MonoidalClosed C] [HasEqualizers C] in
/-- Along an isomorphism `φ`, the unit of `Ext_φ ⊣ Res_φ` is, on underlying objects, the inverse
of the identification `Mod.extendScalarsIsoComapInv` of the extension of scalars with the
restriction of scalars along `φ⁻¹`. -/
lemma extendRestrictAdjunction_unit_app_hom_of_isIso (M : Mod C R) :
    ((extendRestrictAdjunction φ).unit.app M).hom =
      ((extendScalarsIsoComapInv φ).inv.app M).hom := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app (extendRestrictAdjunction φ)
    (comapEquivalenceOfIsIso φ).symm.toAdjunction M
  have h' : (extendRestrictAdjunction φ).unit.app M =
      (comapEquivalenceOfIsIso φ).symm.toAdjunction.unit.app M ≫
        (comap φ).map ((extendScalarsIsoComapInv φ).inv.app M) := by
    rw [← h, Category.assoc, ← Functor.map_comp, extendScalarsIsoComapInv, Iso.hom_inv_id_app,
      Functor.map_id]
    exact (Category.comp_id _).symm
  rw [h', comp_hom']
  simp only [Functor.id_obj, Functor.comp_obj, comapEquivalenceOfIsIso, Equivalence.mk, asIso_inv,
    Equivalence.symm_functor, Equivalence.symm_inverse, Equivalence.toAdjunction_unit,
    Equivalence.symm_unit, Equivalence.counitInv, Iso.trans_inv, Iso.symm_inv, Category.assoc,
    NatTrans.comp_app, comp_hom', comapId_inv_app_hom, comapComp_hom_app_hom, Category.id_comp,
    comap_map_hom]
  exact (Category.id_comp _).trans (Category.id_comp _)

end

section

variable {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] (φ : R ⟶ S) [IsMonHom φ]

omit [MonoidalClosed C] [HasEqualizers C] in
/-- The naturality of the unit of `Ext_φ ⊣ Res_φ`, on underlying objects. -/
@[reassoc]
lemma extendRestrictAdjunction_unit_app_hom_comp_extendScalarsMap_hom {M M' : Mod C R}
    (g : M ⟶ M') :
    ((extendRestrictAdjunction φ).unit.app M).hom ≫ (extendScalarsMap φ g).hom =
      g.hom ≫ ((extendRestrictAdjunction φ).unit.app M').hom :=
  congrArg Hom.hom ((extendRestrictAdjunction φ).unit.naturality g).symm

omit [MonoidalClosed C] [HasEqualizers C] in
/-- The unit of `Ext_φ ⊣ Res_φ`, followed by the extension of a map `c : M ⟶ Res_φ N` and the
counit, is `c`, on underlying objects. -/
lemma extendRestrictAdjunction_unit_app_hom_comp_extendScalarsMap_hom_comp_counit_app_hom
    {M : Mod C R} {N : Mod C S} (c : M ⟶ (comap φ).obj N) :
    ((extendRestrictAdjunction φ).unit.app M).hom ≫ (extendScalarsMap φ c).hom ≫
        ((extendRestrictAdjunction φ).counit.app N).hom = c.hom := by
  have h := congrArg Hom.hom ((extendRestrictAdjunction φ).right_triangle_components N)
  rw [comp_hom', comap_map_hom, id_hom'] at h
  rw [extendRestrictAdjunction_unit_app_hom_comp_extendScalarsMap_hom_assoc]
  erw [h]
  exact Category.comp_id _

end

section

variable {R S R' S' : C} [MonObj R] [MonObj S] [MonObj R'] [MonObj S'] [IsCommMonObj R]
  [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ] (ψ : R' ⟶ S') [IsMonHom ψ]
  (a : R ⟶ R') [IsMonHom a] [IsIso a] (b : S ⟶ S') [IsMonHom b] [IsIso b]
  (sq : a ≫ ψ = φ ≫ b)

omit [MonoidalClosed C] [HasEqualizers C] in
/-- The comparison `Mod.extendScalarsComapIsoOfIsIso` is compatible with the units of the
extension-restriction adjunctions along the isomorphisms `a` and `b`, on underlying objects. -/
@[reassoc]
lemma extendRestrictAdjunction_unit_app_hom_comp_extendScalarsComapIsoOfIsIso_inv_app_hom
    (M : Mod C S) :
    ((extendRestrictAdjunction a).unit.app ((comap φ).obj M)).hom ≫
        ((extendScalarsComapIsoOfIsIso φ ψ a b sq).inv.app M).hom =
      ((extendRestrictAdjunction b).unit.app M).hom := by
  rw [extendRestrictAdjunction_unit_app_hom_of_isIso,
    extendRestrictAdjunction_unit_app_hom_of_isIso]
  simp only [Functor.id_obj, Functor.comp_obj, asIso_inv, extendScalarsComapIsoOfIsIso,
    Iso.trans_inv, Functor.isoWhiskerLeft_inv, Iso.symm_inv, Category.assoc,
    Functor.isoWhiskerRight_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, comp_hom', comapComp_inv_app_hom, comapComp_hom_app_hom,
    comap_map_hom]
  rw [← Category.assoc, ← comp_hom', Iso.inv_hom_id_app]
  exact (Category.id_comp _).trans
    ((Category.id_comp _).trans ((Category.id_comp _).trans (Category.id_comp _)))

end

end CategoryTheory.Mod

namespace CategoryTheory.Functor

/-- The underlying morphism of `mapMod` of a morphism of module objects. -/
lemma mapMod_map_hom' {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal] {A : C} [MonObj A] {M N : Mod C A}
    (g : M ⟶ N) : ((F.mapMod A).map g).hom = F.map g.hom :=
  rfl

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)

attribute [simp] comapPullbackHomCompIso_hom_app_hom

omit [IsCommMonObj Λ] in
/-- The inverse of the comparison `comapPullbackHomCompIso` is the identity on underlying
sheaves. -/
@[simp]
lemma comapPullbackHomCompIso_inv_app_hom
    (N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ((comapPullbackHomCompIso Λ f).inv.app N).hom = 𝟙 _ := by
  simp only [Functor.comp_obj, comapPullbackHomCompIso, Functor.isoWhiskerLeft_trans,
    Iso.trans_inv, Functor.isoWhiskerLeft_inv, Iso.symm_inv, Category.assoc,
    Functor.isoWhiskerRight_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Category.comp_id, Category.id_comp, Mod.comp_hom', Mod.comapComp_hom_app_hom,
    Mod.comap_map_hom, Functor.mapModComapIso_inv_app_hom]
  rfl

/-- **The commutations of the restriction of scalars with the pullbacks and the pushforwards are
mates**: under `f^*_Λ' ⊣ f_*^Λ'` and `f^*_Λ ⊣ f_*^Λ`, the mate of the inverse of
`comapUpperStarIso a f` is `comapLowerStarIso a f`. Both are the identity on underlying sheaves,
up to the units and counits. -/
theorem mateEquiv_comapUpperStarIso_inv :
    mateEquiv (upperStarLowerStarAdjunction Λ' f) (upperStarLowerStarAdjunction Λ f)
      (comapUpperStarIso a f).inv = (comapLowerStarIso a f).hom := by
  refine NatTrans.ext (funext fun N ↦ Mod.hom_ext _ _ ?_)
  rw [comapLowerStarIso, Mod.comapMapModComapIso_hom_app_hom]
  simp only [Functor.comp_obj, upperStarLowerStarAdjunction, comapUpperStarIso, Iso.trans_inv,
    Functor.isoWhiskerRight_inv, Iso.symm_inv, Category.assoc, Functor.isoWhiskerLeft_inv,
    mateEquiv_apply, Adjunction.ofNatIsoRight_unit, Functor.whiskerLeft_comp,
    Functor.whiskerLeft_twice, Functor.whiskerRight_comp, Functor.whiskerRight_twice,
    Adjunction.ofNatIsoRight_counit, Iso.inv_hom_id_assoc, NatTrans.comp_app, Functor.id_obj,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Adjunction.comp_unit_app,
    Functor.comp_map, Functor.mapMod_map, Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.whiskerRight_app, Mod.extendScalars_map, CategoryTheory.Functor.map_id,
    Adjunction.comp_counit_app, Functor.leftUnitor_hom_app, Category.comp_id, Category.id_comp,
    ← Functor.map_comp, Mod.comp_hom', Adjunction.mapModAdjunction_unit_app_hom,
    Mod.comap_map_hom, Mod.homMk_hom, comapPullbackHomCompIso_hom_app_hom, lowerStar_map_hom,
    Mod.id_hom']
  erw [Category.id_comp, Category.id_comp]
  rw [← Functor.map_comp,
    Mod.extendRestrictAdjunction_unit_app_hom_comp_extendScalarsMap_hom_assoc,
    Functor.mapModComapIso_hom_app_hom]
  erw [Category.id_comp]
  rw [Mod.extendRestrictAdjunction_unit_app_hom_comp_extendScalarsComapIsoOfIsIso_inv_app_hom_assoc]
  erw [Mod.extendRestrictAdjunction_unit_app_hom_comp_extendScalarsMap_hom_assoc]
  rw [Mod.extendRestrictAdjunction_unit_app_hom_comp_extendScalarsMap_hom_comp_counit_app_hom]
  simp only [Adjunction.mapModAdjunction_counit_app_hom]
  erw [Functor.mapMod_map_hom', comapPullbackHomCompIso_inv_app_hom,
    CategoryTheory.Functor.map_id, Category.id_comp]
  exact (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).right_triangle_components N.X

/-- **The underived (Pull) is the mate of the commutation of restriction of scalars with the
pullbacks**: under `Ext_{a_Y} ⊣ Res_{a_Y}` and `Ext_{a_X} ⊣ Res_{a_X}`, the mate of
`pullIso a f : f^*_Λ ⋙ Ext_{a_X} ≅ Ext_{a_Y} ⋙ f^*_Λ'` is the inverse of
`comapUpperStarIso a f`. -/
theorem mateEquiv_pullIso_hom :
    mateEquiv (Mod.extendRestrictAdjunction (coefficientMap a Y))
      (Mod.extendRestrictAdjunction (coefficientMap a X)) (pullIso a f).hom =
      (comapUpperStarIso a f).inv := by
  apply (mateEquiv (upperStarLowerStarAdjunction Λ' f)
    (upperStarLowerStarAdjunction Λ f)).injective
  rw [mateEquiv_comapUpperStarIso_inv]
  refine (iterated_mateEquiv_conjugateEquiv _ _ _ _ _).trans ?_
  rw [pullIso, Adjunction.pullIsoOfComapIso, conjugateIsoEquiv_symm_apply_hom,
    Equiv.apply_symm_apply]

/-- **The underived (Pull) is compatible with the units of `Ext ⊣ Res`**: for a
`Λ_Y`-module `M`, the pullback of the unit `M ⟶ Res (Ext M)`, followed by the commutation of
`Res` with the pullbacks, is the unit at `f^* M` followed by `Res` of (Pull). -/
@[reassoc]
theorem upperStar_map_unit_comp_comapUpperStarIso_inv_app
    (M : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (f)^*⟦Λ⟧.map ((Mod.extendRestrictAdjunction (coefficientMap a Y)).unit.app M) ≫
        (comapUpperStarIso a f).inv.app ((Mod.extendScalars (coefficientMap a Y)).obj M) =
      (Mod.extendRestrictAdjunction (coefficientMap a X)).unit.app ((f)^*⟦Λ⟧.obj M) ≫
        (Mod.comap (coefficientMap a X)).map ((pullIso a f).hom.app M) := by
  rw [← mateEquiv_pullIso_hom]
  exact unit_mateEquiv _ _ _ M

end AlgebraicGeometry.ProEtale.CondensedRing
