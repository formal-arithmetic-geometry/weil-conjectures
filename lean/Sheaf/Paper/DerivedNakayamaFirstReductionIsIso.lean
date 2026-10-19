/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module

public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Sheaf.Topology.ProfiniteCondensedRing
import Sheaf.Paper.DerivedNakayamaFirstReductionVanishing
import Sheaf.Paper.DerivedNakayamaFirstReductionTriangles

/-! The reduction-conservativity part of the derived Nakayama first-reduction argument.
Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-lem-pe-derived-nakayama/sk-lem-pe-derived-nakayama-first-reduction.md`
(blueprint: det-pe-derived-nakayama-first-reduction-isIso).
-/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj
open ZeroObject
namespace AlgebraicGeometry.ProEtale

/-- First reduction detects isomorphisms between derived-complete objects.
Source: complete the morphism to a cone triangle, then apply the vanishing part
(blueprint: det-pe-derived-nakayama-first-reduction-isIso). -/
theorem derived_nakayama_first_reduction_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    ∀ (K L : DerivedCategory (AdicCompletion.Modules l E X)) (f : K ⟶ L),
      IsDerivedComplete l E X K → IsDerivedComplete l E X L →
      IsIso ((AdicCompletion.derivedReduction l E X 0).map f) → IsIso f := by
  intro K L f hK hL hf
  obtain ⟨C, g, δ, hT⟩ := distinguished_cocone_triangle f
  have hC := derived_nakayama_first_reduction_triangles l E X _ hT hK hL
  let F := AdicCompletion.derivedReduction l E X 0
  let adj := Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E X 0)
  let := adj.leftAdjointCommShift ℤ
  have := adj.commShift_of_rightAdjoint ℤ
  have := adj.isTriangulated_leftAdjoint
  have hFT := F.map_distinguished _ hT
  have hFC : IsZero (F.obj C) := (Triangle.isZero₃_iff_isIso₁ _ hFT).2 hf
  have hzero := (derived_nakayama_first_reduction_vanishing l E X C hC hFC).2
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1 hzero

end AlgebraicGeometry.ProEtale
