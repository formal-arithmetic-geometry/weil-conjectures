/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Completeness of finite modules over complete Noetherian rings

Source: Stacks Project, Algebra, Lemmas 031B and 00MA (3)
(blueprint: lem-weil-pbc-finite-module-complete-over-complete-noetherian).
-/

@[expose] public section

universe u v

/-- A finite module over a Noetherian adically complete ring is adically complete.
Source: Stacks Project, Algebra, Lemmas 031B and 00MA (3)
(blueprint: lem-weil-pbc-finite-module-complete-over-complete-noetherian).
Proof: identify the completed ring with `R` using the hypothesis that `R` is
`J`-adically complete. Tensoring this identification with `N` identifies
`N` with `AdicCompletion J R ⊗[R] N`. Since `R` is Noetherian and `N` is
finite, the completion-tensor theorem (Stacks 00MA (3), represented by
`lem-weil-pbc-completion-finite-module-tensor`) identifies this tensor product
with `AdicCompletion J N`. Under these identifications the canonical map is
the composite of the two canonical maps, so it is bijective; by
`AdicCompletion.of_bijective_iff`, this is `IsAdicComplete J N`. -/
theorem finite_module_complete_over_complete_noetherian
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (J : Ideal R) [IsAdicComplete J R]
    (N : Type v) [AddCommGroup N] [Module R N] [Module.Finite R N] :
    IsAdicComplete J N := by
  sorry
