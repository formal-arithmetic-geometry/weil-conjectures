/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.RingTheory.RestrictedSeriesPresentation
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Grauert--Remmert finiteness of power-bounded elements

Source: Temkin, Stable modification of relative curves, Theorem 3.5.5, Step 2,
printed p. 22; BGR, Sections 6.4 and 6.4.1/4
(blueprint: lem-trf-valuation-grauert-remmert-powerbounded).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v

open scoped TensorProduct

namespace RestrictedSeries

/-- Power-bounded elements of a reduced affinoid algebra form a finite module over
any topologically finite type integral model with the specified generic fibre.
Source: Temkin, Theorem 3.5.5, Step 2, printed p. 22, quoting BGR 6.4 and 6.4.1/4
(blueprint: lem-trf-valuation-grauert-remmert-powerbounded).

The two open-set conditions express the quotient topology for the Gauss norm on
restricted series. They do not use the coefficientwise topology on formal series,
require a particular equivalent Banach norm on `C`, or require finite relations.
The pure-tensor identity fixes the natural generic-fibre map. The submodule `P` has
exactly the power-bounded elements as its carrier; its module action is the actual
multiplication by elements of `D` in `C`.

Proof (the node's five steps):
1. For `C = 0`, the empty family generates. Otherwise choose a scalar `π` of norm
   strictly between zero and one. Every scalar and every restricted series has bounded
   coefficients, so inverting `π` identifies `K` with `V[1/π]` and the Tate algebra with
   `V⟨T⟩[1/π]`. Localize the model presentation and use the specified generic-fibre
   isomorphism to obtain a continuous Tate presentation whose integral image is `D`.
2. Apply lem-trf-affinoid-distinguished-presentation: reducedness and algebraic
   closedness give finitely many power-bounded `bᵢ` such that every power-bounded
   element is a restricted series in the `bᵢ` with coefficients in `V`.
3. Apply lem-trf-affinoid-powerbounded-integral to the original presentation of step 1.
   Each `bᵢ` satisfies a monic relation over the original model `D`.
4. Repeated monic reduction expresses every monomial in the `bᵢ` in the finite family
   with exponents below the degrees of these relations. All coefficients lie in `D`.
5. By lem-trf-restricted-quotient-complete, `D` is separated and complete for the
   `π`-adic topology. The coefficient series after reduction converge in `D`, since
   the original coefficients tend to zero and every reduction coefficient lies in `D`.
   Continuity into `C` identifies the resulting finite linear combination with the
   original restricted sum. These monomials generate the submodule of power-bounded
   elements, as in def-weil-finitely-generated-module. With no variables the single
   empty monomial is `1`; no nonzero-algebra hypothesis is used. -/
theorem grauert_remmert_powerbounded
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [IsAlgClosed K]
    (V : ValuationSubring K) (hV : ∀ x : K, x ∈ V ↔ ‖x‖ ≤ 1)
    (C : Type v) [NormedCommRing C] [CompleteSpace C] [IsReduced C]
    [Algebra K C] [Algebra V C] [IsScalarTower V K C]
    (haff : ∃ (n : ℕ)
      (q : (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin n ↦ (1 : ℝ))) →+* C),
      Function.Surjective q ∧ q.comp (constants K n) = algebraMap K C ∧
      ∀ U : Set C, IsOpen U ↔ ∀ s, q s ∈ U → ∃ ε : ℝ, 0 < ε ∧
        ∀ t, MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ : Fin n ↦ 1)
          (t.val - s.val) < ε → q t ∈ U)
    (D : Subalgebra V C)
    (hbounded : ∀ d : D, ∃ M : ℝ, ∀ m : ℕ, ‖(d.val : C) ^ m‖ ≤ M)
    (hmodel : ∃ (r : ℕ)
      (q : (MvPowerSeries.IsRestricted.subring (R := V) (fun _ : Fin r ↦ (1 : ℝ))) →+* D),
      Function.Surjective q ∧ q.comp (constants V r) = algebraMap V D ∧
      ∀ U : Set D, IsOpen U ↔ ∀ s, q s ∈ U → ∃ ε : ℝ, 0 < ε ∧
        ∀ t, MvPowerSeries.gaussNorm (norm : V → ℝ) (fun _ : Fin r ↦ 1)
          (t.val - s.val) < ε → q t ∈ U)
    (hgeneric : ∃ e : (D ⊗[V] K) ≃+* C,
      ∀ (d : D) (k : K), e (d ⊗ₜ[V] k) = d.val * algebraMap K C k) :
    ∃ P : Submodule D C,
      (∀ c : C, c ∈ P ↔ ∃ M : ℝ, ∀ m : ℕ, ‖c ^ m‖ ≤ M) ∧ Module.Finite D P := by
  sorry

end RestrictedSeries
