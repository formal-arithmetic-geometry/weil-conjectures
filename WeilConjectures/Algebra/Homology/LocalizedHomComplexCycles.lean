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

import WeilConjectures.Algebra.Homology.LocalizedHomComplexCyclesForward
import WeilConjectures.Algebra.Homology.LocalizedHomComplexCyclesBijective

/-!
# Canonical localized chain maps from section cocycles

## References

* Stacks Project, Tag 0A8X, Hom complexes; Equation 0A8Y (degree zero)
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace CategoryTheory

/-- Degree-zero sections that are cocycles are exactly chain maps on the slice site. -/
theorem localizedHomComplex_cycles_aux
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
    ∃ e : S.cycles 0 ≃ (res.obj L ⟶ res.obj I),
      (∀ (z : S.cycles 0) (p : ℤ) (W : (Over U)ᵒᵖ),
        ((e z).f p).val.app W =
          (((π L I 0 p p (add_zero p)).val.app (op U)) (S.iCycles 0 z)).app W) := by
  intro R₀ H π S res
  classical
  refine (localizedHomComplex_cycles_forward (C := C) J R U L I hzero).elim fun f hf ↦ ?_
  exact ⟨Equiv.ofBijective f
    (localizedHomComplex_cycles_bijective (C := C) J R U L I hzero f hf), hf⟩

end CategoryTheory
