/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.WeilSheaf.Defs

/-!
# Boundary semicontinuity of weights

On a smooth geometrically connected curve `X₀` over `k₀`, the direct image `j_*F` of a lisse
Weil sheaf `F` on a dense open `U₀` has, at every closed point, punctual weights at most every
bound `β` that holds for `F` on `U₀`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- *Boundary semicontinuity of weights.* Let `X₀` be a curve over `k₀` (smooth of relative
dimension one, separated, of finite type and geometrically connected), `j : U₀ ↪ X₀` a dense
open immersion and `F` a lisse Weil sheaf on `U₀` with punctual weights at most `β`. Then the
middle extension `j_*F` has punctual weights at most `β` at every closed point of `X₀`, including
the finitely many points outside `U₀`.
(blueprint: `lem-wf-boundary-semicontinuity`) -/
theorem hasWeightsAtMost_directImage_of_curve {U X : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    [IsDominant j] {ι : PadicAlgCl l →+* ℂ} (F : WeilSheaf k₀ l U) (hF : F.IsLisse) {β : ℝ}
    (hβ : F.HasWeightsAtMost ι β) : ((directImage j).obj F).HasWeightsAtMost ι β := by
  sorry

end AlgebraicGeometry.WeilSheaf
