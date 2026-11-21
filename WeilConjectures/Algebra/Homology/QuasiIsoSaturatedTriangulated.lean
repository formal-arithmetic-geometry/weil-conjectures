/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.MorphismProperty.Retract
import WeilConjectures.Mathlib.Algebra.Homology.Localization

/-!
# Quasi-isomorphisms as a saturated triangulated multiplicative system

## References

* Stacks Project, Tag 04VB
* Stacks Project, Tag 04VD
* Stacks Project, Tag 05R2
* Stacks Project, Tag 05RT
* Stacks Project, Tag 05S8
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Pretriangulated

namespace HomotopyCategory

/-- Quasi-isomorphisms in the homotopy category of integer-indexed cochain complexes form a
saturated multiplicative system compatible with its triangulated structure: left and right
calculi of fractions, compatibility with the triangulation, two-out-of-three, closure under
retracts, and characterization by acyclic cones. -/
theorem quasiIso_saturated_triangulated (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] :
    (quasiIso A (ComplexShape.up ℤ)).HasLeftCalculusOfFractions ∧
    (quasiIso A (ComplexShape.up ℤ)).HasRightCalculusOfFractions ∧
    (quasiIso A (ComplexShape.up ℤ)).IsCompatibleWithTriangulation ∧
    (∀ (W X Y Z : HomotopyCategory A (ComplexShape.up ℤ))
      (f : X ⟶ Y) (g : W ⟶ X) (h : Y ⟶ Z),
      quasiIso A (ComplexShape.up ℤ) (f ≫ h) → quasiIso A (ComplexShape.up ℤ) (g ≫ f) →
        quasiIso A (ComplexShape.up ℤ) f) ∧
    (quasiIso A (ComplexShape.up ℤ)).HasTwoOutOfThreeProperty ∧
    (quasiIso A (ComplexShape.up ℤ)).IsStableUnderRetracts ∧
    (∀ (T : Triangle (HomotopyCategory A (ComplexShape.up ℤ))),
      T ∈ distTriang (HomotopyCategory A (ComplexShape.up ℤ)) →
        (quasiIso A (ComplexShape.up ℤ) T.mor₁ ↔ subcategoryAcyclic A T.obj₃)) ∧
    (DerivedCategory.Qh (C := A)).IsLocalization (quasiIso A (ComplexShape.up ℤ)) ∧
    (DerivedCategory.Qh (C := A)).IsTriangulated := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, inferInstance, inferInstance⟩
  · rw [quasiIso_eq_trW_subcategoryAcyclic]
    infer_instance
  · rw [quasiIso_eq_trW_subcategoryAcyclic]
    infer_instance
  · rw [quasiIso_eq_trW_subcategoryAcyclic]
    infer_instance
  · intro W X Y Z f g h hfh hgf n
    have hfh' : IsIso ((homologyFunctor A (ComplexShape.up ℤ) n).map f ≫
        (homologyFunctor A (ComplexShape.up ℤ) n).map h) := by
      simpa only [Functor.map_comp] using hfh n
    have hgf' : IsIso ((homologyFunctor A (ComplexShape.up ℤ) n).map g ≫
        (homologyFunctor A (ComplexShape.up ℤ) n).map f) := by
      simpa only [Functor.map_comp] using hgf n
    have : Mono ((homologyFunctor A (ComplexShape.up ℤ) n).map f) :=
      mono_of_mono ((homologyFunctor A (ComplexShape.up ℤ) n).map f)
        ((homologyFunctor A (ComplexShape.up ℤ) n).map h)
    have : Epi ((homologyFunctor A (ComplexShape.up ℤ) n).map f) :=
      epi_of_epi ((homologyFunctor A (ComplexShape.up ℤ) n).map g)
        ((homologyFunctor A (ComplexShape.up ℤ) n).map f)
    exact isIso_of_mono_of_epi _
  · infer_instance
  · refine ⟨?_⟩
    intro X Y Z W f g h hg n
    exact MorphismProperty.of_retract (P := MorphismProperty.isomorphisms A)
      (h.map (homologyFunctor A (ComplexShape.up ℤ) n)) (hg n)
  · intro T hT
    rw [quasiIso_eq_trW_subcategoryAcyclic]
    exact (subcategoryAcyclic A).trW_iff_of_distinguished T hT

end HomotopyCategory
