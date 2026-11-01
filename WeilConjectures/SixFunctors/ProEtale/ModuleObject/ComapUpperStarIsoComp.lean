/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsComp
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate

/-!
# The commutation of restriction of scalars with pullback and composition of coefficients

For coefficient changes `a : Λ ⟶ Λ₁`, `b : Λ₁ ⟶ Λ₂` with `a ≫ b = c`, the commutations
`ProEtale.CondensedRing.comapUpperStarIso` of the restrictions of scalars with the pullbacks are
compatible with the transitivity isomorphisms `Mod.comapComp`
(`ProEtale.CondensedRing.comapUpperStarIso_hom_app_comp_map_comapComp`), and so are their derived
versions `ProEtale.CondensedRing.derivedComapLeftDerivedUpperStarIso`
(`map_mapDerivedCategoryComapCompIso_inv_app_comp_derivedComapLeftDerivedUpperStarIso`).
-/

@[expose] public section

set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory Category Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

/-- Transporting a pasting of commutation isomorphisms `σ` along isomorphisms `λ : L ≅ D` to
the commutation isomorphisms `s` determined by `σ⁻¹` and `λ`. -/
lemma map_inv_app_comp_hom_app_comp_map_hom_app_eq {C2Y C1Y C0Y C2X C1X C0X : Type*}
    [Category C2Y] [Category C1Y] [Category C0Y] [Category C2X] [Category C1X] [Category C0X]
    {RbY : C2Y ⥤ C1Y} {RaY : C1Y ⥤ C0Y} {RcY : C2Y ⥤ C0Y}
    {RbX : C2X ⥤ C1X} {RaX : C1X ⥤ C0X} {RcX : C2X ⥤ C0X}
    {L₀ D₀ : C0Y ⥤ C0X} {L₁ D₁ : C1Y ⥤ C1X} {L₂ D₂ : C2Y ⥤ C2X}
    {l₀ : L₀ ≅ D₀} {l₁ : L₁ ≅ D₁} {l₂ : L₂ ≅ D₂}
    {σa : D₁ ⋙ RaX ≅ RaY ⋙ D₀} {σb : D₂ ⋙ RbX ≅ RbY ⋙ D₁} {σc : D₂ ⋙ RcX ≅ RcY ⋙ D₀}
    {TY : RcY ≅ RbY ⋙ RaY} {TX : RcX ≅ RbX ⋙ RaX}
    (H : ∀ K, σc.hom.app K ≫ D₀.map (TY.hom.app K) =
      TX.hom.app (D₂.obj K) ≫ RaX.map (σb.hom.app K) ≫ σa.hom.app (RbY.obj K))
    {sa : RaY ⋙ L₀ ≅ L₁ ⋙ RaX} {sb : RbY ⋙ L₁ ≅ L₂ ⋙ RbX} {sc : RcY ⋙ L₀ ≅ L₂ ⋙ RcX}
    (hsa : ∀ M, sa.hom.app M = l₀.hom.app (RaY.obj M) ≫ σa.inv.app M ≫ RaX.map (l₁.inv.app M))
    (hsb : ∀ M, sb.hom.app M = l₁.hom.app (RbY.obj M) ≫ σb.inv.app M ≫ RbX.map (l₂.inv.app M))
    (hsc : ∀ M, sc.hom.app M = l₀.hom.app (RcY.obj M) ≫ σc.inv.app M ≫ RcX.map (l₂.inv.app M))
    {κY : RbY ⋙ RaY ≅ RcY} {κX : RbX ⋙ RaX ≅ RcX}
    (hκY : ∀ N, κY.inv.app N = TY.hom.app N) (hκX : ∀ N, κX.inv.app N = TX.hom.app N)
    (N : C2Y) :
    L₀.map (κY.inv.app N) ≫ sa.hom.app (RbY.obj N) ≫ RaX.map (sb.hom.app N) =
      sc.hom.app N ≫ κX.inv.app (L₂.obj N) := by
  have H' : D₀.map (TY.hom.app N) ≫ σa.inv.app (RbY.obj N) ≫ RaX.map (σb.inv.app N) =
      σc.inv.app N ≫ TX.hom.app (D₂.obj N) := by
    rw [← cancel_epi (σc.hom.app N), Iso.hom_inv_id_app_assoc, reassoc_of% (H N)]
    simp [← Functor.map_comp]
  have n₁ := l₀.hom.naturality (TY.hom.app N)
  have n₂ := TX.hom.naturality (l₂.inv.app N)
  simp only [Functor.comp_map] at n₂
  rw [hκY, hκX, hsa, hsb, hsc]
  simp only [Functor.map_comp, assoc]
  rw [reassoc_of% n₁, n₂, ← RaX.map_comp_assoc (l₁.inv.app _) (l₁.hom.app _), Iso.inv_hom_id_app,
    Functor.map_id, id_comp, reassoc_of% H']

/-- Inverting an equation `e ≫ x⁻¹ = y⁻¹ ≫ z⁻¹ ≫ w` of isomorphisms. -/
lemma hom_comp_inv_eq_of_hom_comp_inv {C : Type*} [Category C] {A B C₀ D₀ E₀ : C}
    (x : C₀ ≅ B) (e : A ≅ B) (y : D₀ ≅ A) (z : E₀ ≅ D₀) (w : E₀ ≅ C₀)
    (I : e.hom ≫ x.inv = y.inv ≫ z.inv ≫ w.hom) :
    x.hom ≫ e.inv = w.inv ≫ z.hom ≫ y.hom := by
  have I' : e.hom = y.inv ≫ z.inv ≫ w.hom ≫ x.hom := by
    rw [← reassoc_of% I]
    simp
  rw [← cancel_epi w.hom, ← cancel_mono e.hom]
  simp only [assoc, Iso.inv_hom_id, comp_id, Iso.hom_inv_id_assoc]
  rw [I']
  simp

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section OneMap

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The underlying morphism of the inverse of `comapUpperStarIso`: both pullbacks are extensions
of scalars along isomorphisms, identified with restrictions of scalars. -/
lemma comapUpperStarIso_inv_app_hom
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ' Y)) :
    ((comapUpperStarIso a f).inv.app N).hom =
      ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).hom.app
        (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).obj
          ((Mod.comap (coefficientMap a Y)).obj N))).hom ≫
      ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ' f)).inv.app
        (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ' Y)).obj N)).hom := by
  have hn := congrArg Mod.Hom.hom
    ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).hom.naturality
      (((f)^*[Ab.{u + 1}].mapModComapIso (coefficientMap a Y)).hom.app N))
  simp only [Mod.comp_hom', Mod.comap_map_hom,
    Functor.mapModComapIso_hom_app_hom] at hn
  simp only [Functor.comp_obj, Mod.comap_obj_X, comapUpperStarIso,
    Mod.extendScalarsComapIsoOfIsIso, asIso_inv, Mod.comapComp, Mod.comapCongr,
    Functor.isoWhiskerLeft_trans, Functor.isoWhiskerLeft_twice, Functor.mapModComapIso,
    Functor.mapMod_obj_X, Iso.trans_assoc, Iso.self_symm_id_assoc, Iso.trans_inv,
    Functor.isoWhiskerRight_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv, Category.assoc,
    NatTrans.comp_app, Mod.extendScalars_obj, Functor.associator_inv_app,
    Functor.whiskerRight_app, NatIso.ofComponents_hom_app, Mod.extendScalars_map,
    Functor.whiskerLeft_app, Functor.associator_hom_app, NatIso.ofComponents_inv_app,
    Category.comp_id, Category.id_comp, Mod.comp_hom', Mod.id_hom', Mod.isoMk_inv_hom,
    Iso.refl_inv, Mod.isoMk_hom_hom, Iso.refl_hom, Mod.comap_map_hom]
  erw [Category.id_comp]
  erw [Category.comp_id] at hn
  have hh := congrArg (fun k ↦ k ≫
      ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ' f)).inv.app
        (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ' Y)).obj N)).hom) hn
  simpa [Functor.mapModComapIso, Mod.extendScalars, upperStar] using hh

omit [MonObj Λ'] [IsCommMonObj Λ'] [IsMonHom a] in
/-- The underlying morphism of the pullback of a morphism of module objects. -/
lemma upperStar_map_hom
    {M M' : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
    (g : M ⟶ M') :
    ((f)^*⟦Λ⟧.map g).hom =
      ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).hom.app
        (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).obj M)).hom ≫
      (f)^*[Ab.{u + 1}].map g.hom ≫
      ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).inv.app
        (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).obj M')).hom := by
  have hn := congrArg Mod.Hom.hom
    ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).hom.naturality
      (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).map g))
  have h₂ := congrArg Mod.Hom.hom
    ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).hom_inv_id_app
      (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).obj M'))
  rw [Mod.comp_hom', Mod.comp_hom'] at hn
  rw [Mod.comp_hom', Mod.id_hom'] at h₂
  erw [← reassoc_of% hn, h₂]
  exact (comp_id _).symm

end OneMap

section Comp

variable {Λ Λ₁ Λ₂ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ₁] [IsCommMonObj Λ₁] [MonObj Λ₂] [IsCommMonObj Λ₂] (a : Λ ⟶ Λ₁) [IsMonHom a]
  (b : Λ₁ ⟶ Λ₂) [IsMonHom b] (c : Λ ⟶ Λ₂) [IsMonHom c] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The commutations of the restrictions of scalars with the pullbacks are compatible with
the composition of coefficient changes** `a ≫ b = c`, through the transitivity isomorphisms
`Mod.comapComp`. On underlying sheaves all of them are identifications of `f^*` of the
underlying sheaf. -/
lemma comapUpperStarIso_hom_app_comp_map_comapComp
    (hY : coefficientMap a Y ≫ coefficientMap b Y = coefficientMap c Y)
    (hX : coefficientMap a X ≫ coefficientMap b X = coefficientMap c X)
    (N : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ₂ Y)) :
    (comapUpperStarIso c f).hom.app N ≫ (f)^*⟦Λ⟧.map
        (((Mod.comapComp (coefficientMap a Y) (coefficientMap b Y)).symm ≪≫
          Mod.comapCongr hY).inv.app N) =
      ((Mod.comapComp (coefficientMap a X) (coefficientMap b X)).symm ≪≫
          Mod.comapCongr hX).inv.app ((f)^*⟦Λ₂⟧.obj N) ≫
        (Mod.comap (coefficientMap a X)).map ((comapUpperStarIso b f).hom.app N) ≫
        (comapUpperStarIso a f).hom.app ((Mod.comap (coefficientMap b Y)).obj N) := by
  have I : (f)^*⟦Λ⟧.map (((Mod.comapComp (coefficientMap a Y) (coefficientMap b Y)).symm ≪≫
          Mod.comapCongr hY).hom.app N) ≫ (comapUpperStarIso c f).inv.app N =
      (comapUpperStarIso a f).inv.app ((Mod.comap (coefficientMap b Y)).obj N) ≫
        (Mod.comap (coefficientMap a X)).map ((comapUpperStarIso b f).inv.app N) ≫
        ((Mod.comapComp (coefficientMap a X) (coefficientMap b X)).symm ≪≫
          Mod.comapCongr hX).hom.app ((f)^*⟦Λ₂⟧.obj N) := by
    apply Mod.hom_ext
    simp only [Mod.comp_hom', upperStar_map_hom, comapUpperStarIso_inv_app_hom, Mod.comap_map_hom,
      assoc]
    have h₂ := congrArg Mod.Hom.hom
      ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).inv_hom_id_app
        (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).obj
          ((Mod.comap (coefficientMap c Y)).obj N)))
    have h₁ := congrArg Mod.Hom.hom
      ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ₁ f)).inv_hom_id_app
        (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ₁ Y)).obj
          ((Mod.comap (coefficientMap b Y)).obj N)))
    rw [Mod.comp_hom', Mod.id_hom'] at h₁ h₂
    erw [reassoc_of% h₂, reassoc_of% h₁]
    simp [Mod.comapComp, Mod.comapCongr]
  exact hom_comp_inv_eq_of_hom_comp_inv ((comapUpperStarIso c f).app N)
    ((f)^*⟦Λ⟧.mapIso (((Mod.comapComp (coefficientMap a Y) (coefficientMap b Y)).symm ≪≫
      Mod.comapCongr hY).app N))
    ((comapUpperStarIso a f).app ((Mod.comap (coefficientMap b Y)).obj N))
    ((Mod.comap (coefficientMap a X)).mapIso ((comapUpperStarIso b f).app N))
    (((Mod.comapComp (coefficientMap a X) (coefficientMap b X)).symm ≪≫
      Mod.comapCongr hX).app ((f)^*⟦Λ₂⟧.obj N)) I

set_option maxHeartbeats 1000000 in
-- the derived functors on the categories of module objects are slow to unify
/-- **The commutations of the restrictions of scalars with the derived pullbacks are compatible
with the composition of coefficient changes**: for `a ≫ b = c`, under the transitivity
isomorphisms `D(Res_b) ⋙ D(Res_a) ≅ D(Res_c)` (`Mod.mapDerivedCategoryComapCompIso`), the
commutation for `c` is the pasting of those for `a` and `b`. This is the derived form of
`comapUpperStarIso_hom_app_comp_map_comapComp`. -/
lemma map_mapDerivedCategoryComapCompIso_inv_app_comp_derivedComapLeftDerivedUpperStarIso
    (hY : coefficientMap a Y ≫ coefficientMap b Y = coefficientMap c Y)
    (hX : coefficientMap a X ≫ coefficientMap b X = coefficientMap c X)
    (N : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ₂ Y))) :
    L((f)^*⟦Λ⟧).map ((Mod.mapDerivedCategoryComapCompIso (coefficientMap a Y)
        (coefficientMap b Y) (coefficientMap c Y) hY).inv.app N) ≫
      (derivedComapLeftDerivedUpperStarIso a f).hom.app
        (D(Mod.comap (coefficientMap b Y)).obj N) ≫
      D(Mod.comap (coefficientMap a X)).map ((derivedComapLeftDerivedUpperStarIso b f).hom.app N) =
    (derivedComapLeftDerivedUpperStarIso c f).hom.app N ≫
      (Mod.mapDerivedCategoryComapCompIso (coefficientMap a X) (coefficientMap b X)
        (coefficientMap c X) hX).inv.app (L((f)^*⟦Λ₂⟧).obj N) := by
  have H (K) := Functor.mapDerivedCategorySquareIso_hom_app_comp (comapUpperStarIso b f)
      (comapUpperStarIso a f) (comapUpperStarIso c f)
      ((Mod.comapComp (coefficientMap a X) (coefficientMap b X)).symm ≪≫
          Mod.comapCongr hX).symm
      ((Mod.comapComp (coefficientMap a Y) (coefficientMap b Y)).symm ≪≫
          Mod.comapCongr hY).symm
      (comapUpperStarIso_hom_app_comp_map_comapComp a b c f hY hX) K
  refine map_inv_app_comp_hom_app_comp_map_hom_app_eq
    (l₀ := (f)^*⟦Λ⟧.leftDerivedFunctorIsoMapDerivedCategory)
    (l₁ := (f)^*⟦Λ₁⟧.leftDerivedFunctorIsoMapDerivedCategory)
    (l₂ := (f)^*⟦Λ₂⟧.leftDerivedFunctorIsoMapDerivedCategory) H
    (fun M ↦ by simp [derivedComapLeftDerivedUpperStarIso_hom_app,
      Functor.mapDerivedCategoryNatIso_symm])
    (fun M ↦ by simp [derivedComapLeftDerivedUpperStarIso_hom_app,
      Functor.mapDerivedCategoryNatIso_symm])
    (fun M ↦ by simp [derivedComapLeftDerivedUpperStarIso_hom_app,
      Functor.mapDerivedCategoryNatIso_symm])
    (fun _ ↦ by
      simp only [Mod.mapDerivedCategoryComapCompIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
        Functor.mapDerivedCategoryTriangleIso, Iso.trans_hom]
      rw [← Functor.mapDerivedCategoryNatIso_symm])
    (fun _ ↦ by
      simp only [Mod.mapDerivedCategoryComapCompIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
        Functor.mapDerivedCategoryTriangleIso, Iso.trans_hom]
      rw [← Functor.mapDerivedCategoryNatIso_symm])
    N

end Comp

end AlgebraicGeometry.ProEtale.CondensedRing
