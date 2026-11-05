/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Strategy3.ChangeCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsComp

/-! # Independent coefficient/pullback infrastructure: ChangeCoefficientsComp -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.Strategy3

open Scheme

open Scheme

variable {Λ Λ' Λ'' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] [MonObj Λ''] [IsCommMonObj Λ'']
  (a : Λ ⟶ Λ') [IsMonHom a] (b : Λ' ⟶ Λ'') [IsMonHom b] (c : Λ ⟶ Λ'') [IsMonHom c]

omit [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ'] [MonObj Λ''] [IsCommMonObj Λ'']
  [IsMonHom a] [IsMonHom b] [IsMonHom c] in
/-- The coefficient changes compose: `a_X ≫ b_X = c_X` for `a ≫ b = c`. -/
lemma coefficientMap_comp_eq (hc : a ≫ b = c) (X : Scheme.{u}) :
    coefficientMap a X ≫ coefficientMap b X = coefficientMap c X := by
  rw [← coefficientMap_comp, hc]

/-- The composition isomorphism `Res_b ⋙ Res_a ≅ Res_c` of the restrictions of scalars along the
coefficient changes, for `a ≫ b = c`. -/
noncomputable abbrev comapCoefficientMapCompIso (hc : a ≫ b = c) (X : Scheme.{u}) :
    (Mod.comap (coefficientMap b X) :
        Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ'' X) ⥤
          Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X)) ⋙
        Mod.comap (coefficientMap a X) ≅ Mod.comap (coefficientMap c X) :=
  (Mod.comapComp (coefficientMap a X) (coefficientMap b X)).symm ≪≫
    Mod.comapCongr (coefficientMap_comp_eq a b c hc X)

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

omit [IsCommMonObj Λ] [IsCommMonObj Λ'] [IsCommMonObj Λ''] in
/-- The isomorphisms `f_* ⋙ Res ≅ Res ⋙ f_*` compose: the one for `c = a ≫ b` is the composite of
those for `a` and `b`. All of them are the identity on the underlying sheaves. -/
lemma comapLowerStarIso_hom_app_of_comp_eq (hc : a ≫ b = c)
    (K : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ'' X)) :
    (comapLowerStarIso c f).hom.app K =
      (comapCoefficientMapCompIso a b c hc Y).inv.app ((Strategy3.lowerStar Λ'' (f)).obj K) ≫
        (Mod.comap (coefficientMap a Y)).map ((comapLowerStarIso b f).hom.app K) ≫
        (comapLowerStarIso a f).hom.app ((Mod.comap (coefficientMap b X)).obj K) ≫
        (Strategy3.lowerStar Λ (f)).map ((comapCoefficientMapCompIso a b c hc X).hom.app K) := by
  apply Mod.hom_ext
  simp only [lowerStar, Functor.comp_obj, comapLowerStarIso, Mod.comapMapModComapIso_hom_app_hom,
    Iso.trans_inv, Mod.comapCongr, Iso.symm_inv, NatTrans.comp_app, NatIso.ofComponents_inv_app,
    Iso.trans_hom, Iso.symm_hom, NatIso.ofComponents_hom_app, Functor.comp_map, Functor.mapMod_map,
    Mod.comp_hom', Mod.comapComp_inv_app_hom, Mod.isoMk_hom_hom, Iso.refl_hom, Category.comp_id,
    Category.assoc, Mod.isoMk_inv_hom, Iso.refl_inv, Mod.comapComp_hom_app_hom, Mod.comap_map_hom,
    Mod.homMk_hom]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp, Category.id_comp,
    Category.id_comp]
  rfl



end AlgebraicGeometry.ProEtale.Strategy3
