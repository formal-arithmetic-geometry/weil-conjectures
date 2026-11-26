/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import WeilConjectures.RingTheory.FormallySmoothAdic
import WeilConjectures.RingTheory.CompleteLocalMapRegularPresentation
import WeilConjectures.RingTheory.CompleteLocalBaseChangeFiber
import WeilConjectures.RingTheory.FormallySmoothAdicBaseChange
import WeilConjectures.RingTheory.FormallySmoothAdicOfFlatClosedFiber
import WeilConjectures.RingTheory.RegularPresentationFlatFiber

/-!
# Lifting formally smooth complete local algebras from a residue field

A formally smooth complete Noetherian local algebra over the residue field of a complete
Noetherian local ring `A₀` lifts to a formally smooth complete local algebra over `A₀`.

## Implementation details

A regular presentation of `A₀ → E` gives compatible surjections `R → A₀` and `S → E` and a
map `R → S` of complete regular local rings. Cutting `S` down by lifts of parameters of the
kernel of `S ⧸ (t₁, …, t_d) → E` gives a flat complete local `R`-algebra `T` with closed fibre
`E`, so `T` is formally smooth over `R` for its maximal-ideal-adic topology. The base change
`T ⊗[R] A₀` is the required lift, with closed fibre `E`.

## References

* [Stacks, Tag 07NR]
-/

@[expose] public section

universe u v

namespace Algebra

/-- A formally smooth complete local algebra over a residue field lifts to one over
its complete local base: there is a complete Noetherian local `A₀`-algebra `C`, formally
smooth for its maximal-ideal-adic topology, whose closed fibre is isomorphic to `E`. -/
theorem exists_formallySmoothAdic_lift_residue_field
    (A₀ : Type u) [CommRing A₀] [IsNoetherianRing A₀] [IsLocalRing A₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal A₀) A₀]
    (E : Type v) [CommRing E] [IsNoetherianRing E] [IsLocalRing E]
    [IsAdicComplete (IsLocalRing.maximalIdeal E) E]
    [Algebra (IsLocalRing.ResidueField A₀) E]
    [Algebra A₀ E]
    [IsScalarTower A₀ (IsLocalRing.ResidueField A₀) E]
    (hE : FormallySmoothAdic (IsLocalRing.ResidueField A₀) E
      (IsLocalRing.maximalIdeal E)) :
    ∃ (C : Type (max u v)) (_ : CommRing C) (_ : IsNoetherianRing C)
      (_ : IsLocalRing C) (_ : IsAdicComplete (IsLocalRing.maximalIdeal C) C)
      (_ : Algebra A₀ C) (γ : A₀ →+* C),
      algebraMap A₀ C = γ ∧ IsLocalHom γ ∧
      FormallySmoothAdic A₀ C (IsLocalRing.maximalIdeal C) ∧
      ∃ σ : (C ⧸ (IsLocalRing.maximalIdeal A₀).map γ) ≃ₐ[A₀] E,
        ∀ a : A₀,
          σ (Ideal.Quotient.mkₐ A₀ ((IsLocalRing.maximalIdeal A₀).map γ)
            (algebraMap A₀ C a)) = algebraMap A₀ E a := by
  have hlocalE : IsLocalHom (algebraMap A₀ E) := by
    have hcomp : (algebraMap (IsLocalRing.ResidueField A₀) E).comp
        (IsLocalRing.residue A₀) = algebraMap A₀ E := by
      ext a
      exact (IsScalarTower.algebraMap_apply A₀ (IsLocalRing.ResidueField A₀) E a).symm
    rw [← hcomp]
    infer_instance
  obtain ⟨R, S, _, _, _, _, hR, hS, q, v, u, hq, hqLocal, hv, hvLocal,
    huLocal, hcomm, hres, hparams, _, hfiber⟩ :=
    RingHom.exists_complete_local_map_regular_presentation (algebraMap A₀ E)
  have := hR
  have := hS
  have := hqLocal
  have := hvLocal
  have := huLocal
  obtain ⟨T, _, _, _, _, _, hTLocal, hTFlat, e, he, hTFiber⟩ :=
    RingHom.exists_flat_complete_model_of_regular_presentation A₀ E hE R S q v u
      hq hv hcomm hres hparams hfiber
  have := hTLocal
  have halg : (algebraMap R T).toAlgebra = (inferInstance : Algebra R T) := by
    apply Algebra.algebra_ext
    intro r
    rfl
  have hT : FormallySmoothAdic R T (IsLocalRing.maximalIdeal T) := by
    have h := RingHom.formallySmoothAdic_of_flat_closedFiber R T
      (algebraMap R T) hTFlat hTFiber
    rw [halg] at h
    exact h
  let : Algebra R A₀ := q.toAlgebra
  let : Algebra A₀ (TensorProduct R T A₀) := Algebra.TensorProduct.rightAlgebra
  obtain ⟨hC, hCNoeth, hCComplete, hCLocal, hCMax, ⟨σ⟩⟩ :=
    complete_local_baseChange_closedFiber R A₀ T E hq e he
  have := hC
  have := hCNoeth
  have := hCComplete
  have hfs : FormallySmoothAdic A₀ (TensorProduct R T A₀)
      (IsLocalRing.maximalIdeal (TensorProduct R T A₀)) := by
    rw [← hCMax]
    exact formallySmoothAdic_tensorProduct R T A₀ (IsLocalRing.maximalIdeal T) hT
  refine ⟨TensorProduct R T A₀, inferInstance, hCNoeth, hC, hCComplete, inferInstance,
    algebraMap A₀ (TensorProduct R T A₀), rfl, hCLocal, hfs, σ, ?_⟩
  intro a
  exact σ.commutes a

end Algebra
