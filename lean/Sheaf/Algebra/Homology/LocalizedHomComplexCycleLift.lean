/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.Functor

/-!
# Localized Hom-complex cycles

Source: Stacks Project, Tag 0A8X, construction preceding Equation 0A8Y.
This module states the lifting of localized chain maps to cycles.
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace CategoryTheory

/-- A localized chain map lifts to a sectionwise degree-zero cycle.
Source: Stacks Project, Tag 0A8X, construction preceding Equation 0A8Y.
(blueprint: lem-pur-localized-hom-complex-cycle-lift)

Proof: evaluation at U preserves the degree-zero product cone in homComplex_exists.
Each component of g is an internal-Hom section over U, so this product cone supplies
an element x of the evaluated degree-zero term with those projections. Compose the
differential of x with each degree-one projection. The differential formula at n = 0
is postcomposition by d_I minus precomposition by d_L. The chain-map identity of g
makes this difference zero on every slice object. Evaluation also preserves the
degree-one product, whose projections jointly detect zero, so d x = 0. The kernel
universal property of the cycle inclusion supplies z mapping to x. Its projections
are the prescribed components. This uses all integer degrees without boundedness. -/
theorem localizedHomComplex_cycle_lift
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
    ∀ g : (res.obj L ⟶ res.obj I), ∃ z : S.cycles 0,
      ∀ (p : ℤ) (W : (Over U)ᵒᵖ),
        (((π L I 0 p p (add_zero p)).val.app (op U)) (S.iCycles 0 z)).app W =
          (g.f p).val.app W := by sorry

end CategoryTheory
