/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
import WeilConjectures.AlgebraicGeometry.ClosedImmersionTwistCohomologyBound
import WeilConjectures.AlgebraicGeometry.ClosedImmersionTwistVanishingStep

/-! # Fixed-degree projective Serre vanishing

## References

* Stacks Project, Tag 01YS
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- Fixed-degree projective Serre vanishing, split from the affine restriction theorem.
(Stacks, Tag 01YS (4)). -/
theorem exists_isZero_closedImmersion_twist_degree
    (A : Type u) [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} {N : ℕ}
    (i : X ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of A))) [IsClosedImmersion i]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] (q : ℕ) (hq : 0 < q) :
    ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace q).obj
        (tensorObj F (ProjectiveSpace.twistRestrict i t))) := by
  let P (r : ℕ) : Prop := ∀ {Y : Scheme.{u}}
    (j : Y ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of A))) [IsClosedImmersion j]
    (G : Y.Modules) [G.IsQuasicoherent]
    [G.IsFinitePresentation], ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
      IsZero ((RingedSpace.moduleCohomology Y.toRingedSpace r).obj
        (tensorObj G (ProjectiveSpace.twistRestrict j t)))
  have hbase (r : ℕ) (hr : N < r) : P r := by
    intro Y j _ G _ _
    exact ⟨0, fun t _ ↦ isZero_closedImmersion_twist_above_dimension A j G r t hr⟩
  by_cases hlarge : N < q
  · exact hbase q hlarge i F
  · have hqN : q ≤ N + 1 := by omega
    have hd : P q := Nat.decreasingInduction' (P := P) (n := N + 1) (m := q)
      (fun r _ hqr hn Y j _ G _ _ ↦
        exists_isZero_closedImmersion_twist_of_next_degree
          A j r (by omega) hn G) hqN (hbase (N + 1) (by omega))
    exact hd i F

end AlgebraicGeometry.Scheme.Modules
