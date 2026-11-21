/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.Algebra.Homology.LocalizedHomComplexCycleLift

/-!
# Localized Hom-complex cycles

This module proves bijectivity from product injectivity and cycle lifting.

## References

* Stacks Project, Tag 0A8X, construction preceding Equation 0A8Y
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency true in
-- Evaluated product projections unfold composed functors and restriction wrappers.
/-- A function with the localized cycle projection formula is bijective. -/
theorem localizedHomComplex_cycles_bijective
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{max u v}) (U : C)
    (L I : CochainComplex (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ)
    (hzero : Functor.PreservesZeroMorphisms
      (SheafOfModules.overFunctor.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R) U)) :
    let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
    let H := homComplex (R := R) L I
    let π := Classical.choose (Classical.choose_spec
      (homComplex_exists.{u, v, max u v, max u v} (J := J) (R := R)))
    let S := ((SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
      forget₂ (ModuleCat.{max u v} (R₀.obj.obj (op U))) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj H
    letI := hzero
    let res : CochainComplex (SheafOfModules.{max u v} R₀) ℤ ⥤
        CochainComplex (SheafOfModules.{max u v} (R₀.over U)) ℤ :=
      (SheafOfModules.overFunctor.{max u v} R₀ U).mapHomologicalComplex (ComplexShape.up ℤ)
    ∀ f : S.cycles 0 → (res.obj L ⟶ res.obj I),
      (∀ (z : S.cycles 0) (p : ℤ) (W : (Over U)ᵒᵖ),
        ((f z).f p).val.app W =
          (((π L I 0 p p (add_zero p)).val.app (op U)) (S.iCycles 0 z)).app W) →
      Function.Bijective f := by
  classical
  dsimp only
  intro f hf
  let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
  let H := homComplex (R := R) L I
  let π := Classical.choose (Classical.choose_spec
    (homComplex_exists.{u, v, max u v, max u v} (J := J) (R := R)))
  let E := SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
    forget₂ (ModuleCat.{max u v} (R₀.obj.obj (op U))) AddCommGrpCat
  let S := (E.mapHomologicalComplex (ComplexShape.up ℤ)).obj H
  let := hzero
  refine ⟨?_, ?_⟩
  · intro z z' hzz'
    apply (AddCommGrpCat.mono_iff_injective (S.iCycles 0)).mp inferInstance
    let T := E ⋙ forget AddCommGrpCat
    let c := Limits.Fan.mk (H.X 0) (fun p : ℤ ↦ π L I 0 p (p + 0) rfl)
    have hc : Limits.IsLimit c := (Classical.choose_spec (Classical.choose_spec
      (homComplex_exists.{u, v, max u v, max u v} (J := J) (R := R)))).1 L I 0
        |>.some
    have ht := (Limits.Fan.isLimitMapConeEquiv T _ c) (Limits.isLimitOfPreserves T hc)
    have he : (↾fun _ : PUnit ↦ S.iCycles 0 z) =
        (↾fun _ : PUnit ↦ S.iCycles 0 z') := by
      apply ht.hom_ext
      intro ⟨p⟩
      apply ConcreteCategory.hom_ext
      intro t
      change ((π L I 0 p (p + 0) rfl).val.app (op U)) (S.iCycles 0 z) =
        ((π L I 0 p (p + 0) rfl).val.app (op U)) (S.iCycles 0 z')
      apply PresheafOfModules.hom_ext
      intro W
      have hh := (hf z p W).symm.trans
        ((congrArg (fun g ↦ ((g.f p).val.app W)) hzz').trans (hf z' p W))
      cases p <;> exact hh
    exact ConcreteCategory.congr_hom he PUnit.unit
  · intro g
    obtain ⟨z, hz⟩ := localizedHomComplex_cycle_lift J R U L I hzero g
    refine ⟨z, ?_⟩
    apply HomologicalComplex.hom_ext
    intro p
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    exact (hf z p W).trans (hz p W)


end CategoryTheory
