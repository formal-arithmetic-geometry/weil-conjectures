/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionDerivedPull
import WeilConjectures.AlgebraicGeometry.ConstantCompletionOrdinaryReducedPullTransport

/-!
# Ordinary finite reduction of constant-to-completed scalar insertion

Source: Stacks Project, sites-modules.tex, Tags 03EK, 03EL, 093M;
sites-cohomology.tex, Tag 06YY.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ConstantCompletion

variable {C C' : Type u} [SmallCategory C] [SmallCategory C']
variable {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
variable {L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)} (F : InverseImageData L)

/-- Ordinary scalar insertion becomes invertible after extension to a finite quotient
(Stacks, Tags 03EK, 03EL, 093M and 06YY). -/
theorem ordinaryReducedPull_isIso
    (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (n : ℕ) :
    IsIso (Functor.whiskerRight (ordinaryPullComparison F A I)
      (change (quotient J' A I n))) := by
  let _adj := adj
  obtain ⟨X, s, t, h⟩ := ordinaryReducedPull_transport F V adj A I n
  have hi : IsIso (Functor.whiskerRight (ordinaryPullComparison F A I)
      (change (quotient J' A I n)) ≫ t.hom) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right
    (Functor.whiskerRight (ordinaryPullComparison F A I)
      (change (quotient J' A I n))) t.hom

end CategoryTheory.ConstantCompletion
