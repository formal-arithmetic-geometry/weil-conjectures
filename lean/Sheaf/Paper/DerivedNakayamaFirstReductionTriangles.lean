/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module

public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

import Sheaf.Paper.DerivedNakayamaFirstReductionShifts
import Sheaf.Paper.DerivedNakayamaRoosFunctor
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Sheaf.Topology.ProfiniteCondensedRing

/-! The cone-closure part of the derived Nakayama first-reduction argument.
Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-lem-pe-derived-nakayama/sk-lem-pe-derived-nakayama-first-reduction.md`
(blueprint: det-pe-derived-nakayama-first-reduction-triangles).
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace AlgebraicGeometry.ProEtale

/-- Derived completeness is closed under the third vertex of a distinguished triangle.
Source: the cone comparison and the two-isomorphism criterion
(blueprint: det-pe-derived-nakayama-first-reduction-triangles). -/
theorem derived_nakayama_first_reduction_triangles
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    ∀ T : Triangle (DerivedCategory (AdicCompletion.Modules l E X)),
      T ∈ distTriang (DerivedCategory (AdicCompletion.Modules l E X)) →
      IsDerivedComplete l E X T.obj₁ → IsDerivedComplete l E X T.obj₂ →
        IsDerivedComplete l E X T.obj₃ := by
  intro T hT h₁ h₂
  obtain ⟨P, hP, ⟨eP⟩, haugP⟩ := h₁
  obtain ⟨B, hB, ⟨eB⟩, haugB⟩ := h₂
  obtain ⟨R, s, hs, g, hg⟩ := DerivedCategory.right_fac
    (eP.hom ≫ T.mor₁ ≫ eB.inv)
  obtain ⟨W, t, ht, _, hW⟩ := CochainComplex.exists_quasiIso_flat_kFlat R
  have := ht
  have := hs
  let a : DerivedCategory.Q.obj W ≅ T.obj₁ :=
    asIso (DerivedCategory.Q.map t) ≪≫ asIso (DerivedCategory.Q.map s) ≪≫ eP
  let f : W ⟶ B := t ≫ g
  have hc : DerivedCategory.Q.map f ≫ eB.hom = a.hom ≫ T.mor₁ := by
    have h := congrArg (fun q ↦ DerivedCategory.Q.map s ≫ q ≫ eB.hom) hg
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] at h
    dsimp [a, f]
    simp only [Functor.map_comp, Category.assoc]
    rw [← h]
  have hWa : IsIso (DerivedCategory.Q.map (AdicCompletion.augmentation l E X W)) := by
    have hcomp := (AdicCompletion.isDerivedComplete_iff l E X T.obj₁ W hW a).1
      ⟨P, hP, ⟨eP⟩, haugP⟩
    exact (isIso_comp_left_iff a.inv _).1 hcomp
  have hWc : IsDerivedComplete l E X (DerivedCategory.Q.obj W) :=
    ⟨W, hW, ⟨Iso.refl _⟩, hWa⟩
  have hWsh := derived_nakayama_first_reduction_shifts l E X
    (DerivedCategory.Q.obj W) hWc (1 : ℤ)
  have hWshflat := (CochainComplex.kFlat_shift_iff W (1 : ℤ)).2 hW
  let esh := (DerivedCategory.Q.commShiftIso (1 : ℤ)).app W
  have hWsha : IsIso (DerivedCategory.Q.map
      (AdicCompletion.augmentation l E X (W⟦(1 : ℤ)⟧))) := by
    have hcomp := (AdicCompletion.isDerivedComplete_iff l E X _ _ hWshflat esh).1 hWsh
    exact (isIso_comp_left_iff esh.inv _).1 hcomp
  have hconeaug := AdicCompletion.roos_augmentation_cone l E X f haugB hWsha
  have hconeFlat : (HomologicalComplex.quasiIso
      (AdicCompletion.Modules l E X) (.up ℤ)).kFlat (CochainComplex.mappingCone f) := by
    apply (HomotopyCategory.kFlat_quotient_obj_iff _).1
    exact (HomotopyCategory.quasiIso (AdicCompletion.Modules l E X) (.up ℤ)).kFlat
      |>.ext_of_isTriangulatedClosed₃ (CochainComplex.mappingCone.triangleh f)
        (HomotopyCategory.mappingCone_triangleh_distinguished f)
        ((HomotopyCategory.kFlat_quotient_obj_iff _).2 hW)
        ((HomotopyCategory.kFlat_quotient_obj_iff _).2 hB)
  let j := Pretriangulated.isoTriangleOfIso₁₂
    (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)) T
    (DerivedCategory.mappingCone_triangle_distinguished f) hT a eB hc
  exact ⟨CochainComplex.mappingCone f, hconeFlat,
    ⟨(Triangle.π₃.mapIso j)⟩, hconeaug⟩

end AlgebraicGeometry.ProEtale
