/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.CompositionModelOrientationDefinitions
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.PurityCompositionCompatibleDncCharts
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Logic.Small.Defs

/-! # The beta-delta calculation in one compatible DNC coordinate triple -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v₁ v₂ v₃ u₁ u₂ u₃
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

private theorem tensor_comp {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    (F : C ⥤ D ⥤ E) {K K' K'' : C} {L L' L'' : D}
    (a : K ≅ K') (a' : K' ≅ K'') (b : L ≅ L') (b' : L' ≅ L'') :
    compatibleBifunctorIso F a b ≪≫ compatibleBifunctorIso F a' b' =
      compatibleBifunctorIso F (a ≪≫ a') (b ≪≫ b') := by
  ext
  simp only [compatibleBifunctorIso, Functor.mapIso_trans, NatIso.trans_app, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc]
  change (F.map a.hom).app L ≫ (F.obj K').map b.hom ≫
    (F.map a'.hom).app L' ≫ (F.obj K'').map b'.hom =
      (F.map a.hom).app L ≫ (F.map a'.hom).app L ≫
        (F.obj K'').map b.hom ≫ (F.obj K'').map b'.hom
  rw [(F.map a'.hom).naturality_assoc]
end WeilConjectures.PurityFiniteSetting
