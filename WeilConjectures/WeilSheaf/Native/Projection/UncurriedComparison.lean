/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import WeilConjectures.CategoryTheory.Functor.CurryComparison

/-! # Uncurried tensor comparisons -/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Functor

variable {A B A' B' : Type*} [Category* A] [Category* B]
  [Category* A'] [Category* B']

/-- Uncurry a comparison with a functor, simplifying the functorial composition maps. -/
def uncurryCompIsoOfIso {TA : A ⥤ A ⥤ A} {TB : B ⥤ B ⥤ B} {R : B ⥤ A}
    (e : (postcompose₂.obj R).obj TB ≅ (((whiskeringLeft₂ A).obj R).obj R).obj TA) :
    uncurry.obj TB ⋙ R ≅ R.prod R ⋙ uncurry.obj TA :=
  NatIso.ofComponents (fun MN ↦ (e.app MN.1).app MN.2) (fun f ↦ by
    have h := (uncurry.map e.hom).naturality f
    dsimp at h ⊢
    simpa only [map_comp] using h)

set_option backward.isDefEq.respectTransparency false in
/-- The uncurried form of compatibility, with the pullback comparison pointing towards
the realized pullback. -/
lemma comparisonCompatible_uncurried
    {R : B ⥤ A} {R' : B' ⥤ A'} {FA : A ⥤ A'} {FB : B ⥤ B'}
    {TA : A × A ⥤ A} {TB : B × B ⥤ B}
    {TA' : A' ⥤ A' ⥤ A'} {TB' : B' ⥤ B' ⥤ B'}
    (eR : R ⋙ FA ≅ FB ⋙ R')
    (tA : TA ⋙ FA ≅ FA.prod FA ⋙ uncurry.obj TA')
    (tB : TB ⋙ FB ≅ FB.prod FB ⋙ uncurry.obj TB')
    (rho : TB ⋙ R ≅ R.prod R ⋙ TA)
    (rho' : (postcompose₂.obj R').obj TB' ≅
      (((whiskeringLeft₂ A').obj R').obj R').obj TA')
    (h : Adjunction.ComparisonCompatible eR.symm (curryCompIsoOfIso rho).hom rho'.hom
      (curryCompIsoOfIso' tA) (curryCompIsoOfIso' tB)) (M N : B) :
    FA.map (rho.hom.app (M, N)) ≫ tA.hom.app (R.obj M, R.obj N) ≫
        (uncurry.obj TA').map (Prod.mkHom (eR.hom.app M) (eR.hom.app N)) =
      eR.hom.app (TB.obj (M, N)) ≫ R'.map (tB.hom.app (M, N)) ≫
        (rho'.hom.app (FB.obj M)).app (FB.obj N) := by
  have hh := h M N
  change FA.map (rho.hom.app (M, N)) ≫ tA.hom.app (R.obj M, R.obj N) =
    eR.hom.app (TB.obj (M, N)) ≫ R'.map (tB.hom.app (M, N)) ≫
      (rho'.hom.app (FB.obj M)).app (FB.obj N) ≫
        (TA'.map (eR.inv.app M)).app _ ≫ (TA'.obj _).map (eR.inv.app N) at hh
  rw [← Category.assoc, hh]
  change _ ≫ (uncurry.obj TA').map (Prod.mkHom (eR.hom.app M) (eR.hom.app N)) = _
  have hc : (uncurry.obj TA').map (Prod.mkHom (eR.inv.app M) (eR.inv.app N)) ≫
      (uncurry.obj TA').map (Prod.mkHom (eR.hom.app M) (eR.hom.app N)) = 𝟙 _ := by
    rw [← Functor.map_comp]
    convert (uncurry.obj TA').map_id _ using 1
    congr 1
    ext <;> simp
  simpa only [uncurry_obj_map, uncurry_obj_obj, Functor.comp_obj, Category.assoc,
    Category.comp_id] using
    congrArg (fun z ↦ eR.hom.app (TB.obj (M, N)) ≫ R'.map (tB.hom.app (M, N)) ≫
      (rho'.hom.app (FB.obj M)).app (FB.obj N) ≫ z) hc

end CategoryTheory.Functor
