/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.HomotopyCategory
import WeilConjectures.Algebra.Homology.LocalizedHomComplexCycles
import WeilConjectures.Algebra.Homology.LocalizedHomComplexHomology

/-!
# Sections of the sheaf Hom complex and homotopy classes

## References

* Stacks Project, Tag 0A8Y, Equation (21.34.0.1), used in Tag 0A94
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace CategoryTheory

/-- The degree-zero cycles of the section Hom complex identify with localized chain
maps, and its degree-zero homology identifies with their homotopy classes. No
K-injectivity or derived category is needed. -/
theorem localizedHomComplex_homotopy
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
    let q := HomotopyCategory.quotient
      (SheafOfModules.{max u v} (R₀.over U)) (ComplexShape.up ℤ)
    ∃ e : S.cycles 0 ≃ (res.obj L ⟶ res.obj I),
      (∀ (z : S.cycles 0) (p : ℤ) (W : (Over U)ᵒᵖ),
        ((e z).f p).val.app W =
          (((π L I 0 p p (add_zero p)).val.app (op U)) (S.iCycles 0 z)).app W) ∧
      ∃ a : S.homology 0 ≃ (q.obj (res.obj L) ⟶ q.obj (res.obj I)),
        ∀ z : S.cycles 0, a (S.homologyπ 0 z) = q.map (e z) := by
  classical
  let hcyc := localizedHomComplex_cycles_aux (C := C) J R U L I hzero
  rcases hcyc with ⟨e, he⟩
  refine ⟨e, he, ?_⟩
  exact localizedHomComplex_homology_aux (C := C) J R U L I hzero e he

end CategoryTheory
