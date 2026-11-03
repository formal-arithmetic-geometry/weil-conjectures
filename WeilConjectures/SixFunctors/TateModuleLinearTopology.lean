/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.GroupTheory.TateModule
public import Mathlib.Topology.Constructions
import WeilConjectures.Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.NumberTheory.Padics.ProperSpace

/-! # Linear coordinates for the inverse-limit topology on a Tate module -/

@[expose] public section
set_option autoImplicit false
universe u
open Topology

/-- Finite linear coordinates on a Tate module are homeomorphic coordinates for its
inverse-limit topology. For a fixed t, the nth coordinate of a scalar multiple a*t
factors through a mod r^n, so scalar multiplication by t is continuous. Express the
inverse linear equivalence as a finite sum of scalar multiples of basis vectors.
It is continuous, and compactness of the finite power of the adic integers and
Hausdorffness of the coordinate product imply continuity of its inverse.
Source: step 4 of the elliptic multiplication-tower argument in the scope remark.
(blueprint: lem-sf-tate-module-linear-topology) -/
theorem tateModuleLinearTopology (r : ℕ) [Fact r.Prime]
    (M : Type u) [AddCommGroup M] (d : ℕ)
    (e : AddCommGroup.tateModule r M ≃ₗ[ℤ_[r]] (Fin d → ℤ_[r])) :
    let : TopologicalSpace (AddCommGroup.tateModule r M) :=
      TopologicalSpace.induced (fun t : AddCommGroup.tateModule r M ↦ (t : ℕ → M))
        (@Pi.topologicalSpace ℕ (fun _ ↦ M) (fun _ ↦ ⊥))
    Continuous e ∧ Continuous e.symm := by
  classical
  let : TopologicalSpace M := ⊥
  let : TopologicalSpace (AddCommGroup.tateModule r M) :=
    TopologicalSpace.induced (fun t : AddCommGroup.tateModule r M ↦ (t : ℕ → M))
      inferInstance
  have : DiscreteTopology M := ⟨rfl⟩
  have hs (t : AddCommGroup.tateModule r M) :
      Continuous (fun a : ℤ_[r] ↦ a • t) := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro n
    have h := (continuous_of_discreteTopology :
      Continuous (fun z : ZMod (r ^ n) ↦ (z.val : ℤ) • (t : ℕ → M) n)).comp
        (PadicInt.continuous_toZModPow n)
    convert h using 1
    funext a
    exact (AddCommGroup.tateModule.appr_zsmul_coe_eq t a
      (x := ((PadicInt.toZModPow n a).val : ℤ))
      (by rw [Int.cast_natCast, ZMod.natCast_zmod_val]))
  have hei : Continuous e.symm := by
    have hsum (v : Fin d → ℤ_[r]) :
        e.symm v = ∑ i, v i • e.symm (Pi.single i 1) := by
      conv_lhs => rw [pi_eq_sum_univ' v]
      simp only [map_sum, map_smul]
    convert continuous_finsetSum Finset.univ
      (fun i _ ↦ (hs (e.symm (Pi.single i 1))).comp (continuous_apply i)) using 1
    funext v
    exact hsum v
  have : T2Space (AddCommGroup.tateModule r M) :=
    inferInstanceAs (T2Space (↥(AddCommGroup.tateModule r M)))
  exact ⟨hei.continuous_symm_of_equiv_compact_to_t2 (f := e.symm.toEquiv), hei⟩
