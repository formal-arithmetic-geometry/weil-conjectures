/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module

public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

import Sheaf.Paper.DerivedNakayamaRoosShiftComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Sheaf.Topology.ProfiniteCondensedRing

/-! The shift-closure part of the derived Nakayama first-reduction argument.
Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-lem-pe-derived-nakayama/sk-lem-pe-derived-nakayama-first-reduction.md`
(blueprint: det-pe-derived-nakayama-first-reduction-shifts).
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace AlgebraicGeometry.ProEtale

/-- Derived completeness is preserved by every integer shift.
Source: the signed shift comparison for the Roos completion model
(blueprint: det-pe-derived-nakayama-first-reduction-shifts). -/
theorem derived_nakayama_first_reduction_shifts
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    ∀ K : DerivedCategory (AdicCompletion.Modules l E X),
      IsDerivedComplete l E X K → ∀ r : ℤ,
        IsDerivedComplete l E X (K⟦r⟧) := by
  intro K hK r
  obtain ⟨P, hP, ⟨e⟩, haug⟩ := hK
  obtain ⟨j, hj⟩ := derived_nakayama_roos_shift_comparison l E X P r
  refine ⟨P⟦r⟧, (CochainComplex.kFlat_shift_iff P r).2 hP,
    ⟨(DerivedCategory.Q.commShiftIso r).app P ≪≫
      (shiftFunctor _ r).mapIso e⟩, ?_⟩
  have : QuasiIso (AdicCompletion.augmentation l E X P) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (AdicCompletion.Modules l E X) _).1 haug
  have hshift : IsIso (DerivedCategory.Q.map
      ((AdicCompletion.augmentation l E X P)⟦r⟧')) := by infer_instance
  have heq := congrArg (fun f ↦ DerivedCategory.Q.map f) hj
  rw [Functor.map_comp] at heq
  rw [← isIso_comp_right_iff _ (DerivedCategory.Q.map j.hom), heq]
  exact hshift

end AlgebraicGeometry.ProEtale
