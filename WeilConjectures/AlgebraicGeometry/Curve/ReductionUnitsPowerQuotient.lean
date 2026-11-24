/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.ReductionUnitsPowerKernel
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.Curve.ReductionUnitsPowerCokernel

/-! # Successive quotients of the nilpotent-units sheaves
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- Consecutive nilpotent-units sheaves have an additive quasi-coherent quotient.
This single-step statement needs neither a global nilpotence exponent nor a
Noetherian hypothesis, and concerns only sheaves on X, before reduction pullback. -/
theorem exists_reduction_units_power_quotient (X : Scheme.{u}) (j : ℕ) :
    ∃ (F : X.Modules) (_ : F.IsQuasicoherent)
      (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
      S.ShortExact ∧ Nonempty (S.X₁ ≅ X.reductionUnitsPowerKernel (j + 1)) ∧
      Nonempty (S.X₂ ≅ X.reductionUnitsPowerKernel j) ∧
      Nonempty (S.X₃ ≅
        ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
          (Modules.etaleTensorSectionsSheaf F))) := by
  let F := X.reductionIdealPowerQuotient j
  let f := X.reductionUnitsPowerInclusion j
  let S := ShortComplex.cokernelSequence f
  have hS : S.ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact f
      mono_f := by
        change Mono f
        exact mono_reductionUnitsPowerInclusion X j }
  refine ⟨F, inferInstance, S, hS, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩, ?_⟩
  exact nonempty_reductionUnitsPowerCokernelIso X j

end AlgebraicGeometry.Scheme
