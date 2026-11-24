/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentIntegralFiltration
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent
import WeilConjectures.AlgebraicGeometry.CoherentIntegralFiltrationBiproductSucc
import WeilConjectures.AlgebraicGeometry.PushforwardFinSumSuccIso

/-! The split-sum induction step for coherent integral filtrations.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Appending one summand to a coherent integral-ideal filtration. -/
theorem coherentIntegralFiltration_ideal_sum_succ
    {X Z : Scheme.{u}} [IsLocallyNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (r : ℕ) (I : Z.IdealSheafData) (hne : I ≠ ⊥)
    (hI : RingedSpace.IsCoherent Z.toRingedSpace I.toModules)
    (hprev : HasCoherentIntegralFiltration
      ((pushforward i).obj (∐ fun _ : Fin r => I.toModules))) :
    HasCoherentIntegralFiltration
      ((pushforward i).obj (∐ fun _ : Fin (r + 1) => I.toModules)) := by
  let A : X.Modules := (pushforward i).obj I.toModules
  have hA : RingedSpace.IsCoherent X.toRingedSpace A :=
    (isCoherent_pushforward_of_isFinite i I.toModules hI).1
  have hAw : ∃ (Z : Scheme.{u}) (j : Z ⟶ X), IsClosedImmersion j ∧ IsIntegral Z ∧
      ∃ J : Z.IdealSheafData, J ≠ ⊥ ∧
        RingedSpace.IsCoherent Z.toRingedSpace J.toModules ∧
        Nonempty (A ≅ (pushforward j).obj J.toModules) := by
    refine ⟨Z, i, inferInstance, inferInstance, I, hne, hI, ?_⟩
    exact ⟨Iso.refl _⟩
  obtain ⟨e⟩ := pushforward_fin_sum_succ_iso i r I
  exact hasCoherentIntegralFiltration_of_biproduct _ _ _ hprev hA hAw e

end AlgebraicGeometry.Scheme.Modules
