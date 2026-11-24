/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Finiteness.Small

/-!
# Completeness of finite modules over complete Noetherian rings

## References

* Stacks Project, Algebra, Tags 031B and 00MA (3).
-/

@[expose] public section

universe u v

private theorem finiteModuleCompleteSameUniverse
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (J : Ideal R) [IsAdicComplete J R]
    (N : Type u) [AddCommGroup N] [Module R N] [Module.Finite R N] :
    IsAdicComplete J N := by
  let e := (TensorProduct.lid R N).symm.trans
    (TensorProduct.congr (AdicCompletion.ofLinearEquiv J R) (LinearEquiv.refl R N))
  have h : (AdicCompletion.of J N : N → AdicCompletion J N) =
      (AdicCompletion.ofTensorProduct J N) ∘ e := by
    funext x
    simp only [e, LinearEquiv.trans_apply, TensorProduct.lid_symm_apply,
      TensorProduct.congr_tmul, AdicCompletion.ofLinearEquiv_apply,
      LinearEquiv.refl_apply, Function.comp_apply, AdicCompletion.ofTensorProduct_tmul]
    have h1 : AdicCompletion.of J R 1 = 1 :=
      by simpa using (AdicCompletion.algebraMap_apply (S := R) J (1 : R)).symm
    rw [h1, one_smul]
  apply AdicCompletion.of_bijective_iff.mp
  rw [h]
  exact (AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian J N).comp
    e.bijective

/-- A finite module over a Noetherian adically complete ring is adically complete. -/
theorem finite_module_complete_over_complete_noetherian
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (J : Ideal R) [IsAdicComplete J R]
    (N : Type v) [AddCommGroup N] [Module R N] [Module.Finite R N] :
    IsAdicComplete J N := by
  let : Small.{u} N := Module.Finite.small R N
  let f := Shrink.linearEquiv R N
  let : IsAdicComplete J (Shrink.{u} N) :=
    finiteModuleCompleteSameUniverse R J (Shrink.{u} N)
  let e := f.symm.trans ((AdicCompletion.ofLinearEquiv J (Shrink.{u} N)).trans
    ((AdicCompletion.congr J f).restrictScalars R))
  apply AdicCompletion.of_bijective_iff.mp
  have h : (AdicCompletion.of J N : N → AdicCompletion J N) = e := by
    funext x
    simp [e, AdicCompletion.congr_apply, AdicCompletion.map_of]
  rw [h]
  exact e.bijective
