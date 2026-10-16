/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.Logic.Equiv.Set
public import Mathlib.Data.Fintype.Basic

/-!
# Splitting finite index sets along an injection

The coefficient-independent equivalence and its inverse equation are extracted unchanged
from `WeilConjectures.SixFunctors.ProEtale.Adic.UnitMatrix` so continuous matrix arguments
can reuse them without importing either pro-étale inverse-image API.
(blueprint: def-weil-pbc-finite-index-splitting).
-/

@[expose] public section

namespace PadicAlgCl

variable {κ : Type*} [DecidableEq κ]

/-- The splitting `κ ≃ Fin r ⊕ (κ ∖ range ρ)` along an injection `ρ : Fin r → κ`. -/
noncomputable def sumComplEquiv {r : ℕ} (ρ : Fin r → κ) (hρ : Function.Injective ρ) :
    κ ≃ Fin r ⊕ {i // i ∉ Set.range ρ} :=
  (Equiv.sumCompl (· ∈ Set.range ρ)).symm.trans
    (Equiv.sumCongr (Equiv.ofInjective ρ hρ).symm (Equiv.refl _))

@[simp]
lemma sumComplEquiv_symm_inl {r : ℕ} (ρ : Fin r → κ) (hρ : Function.Injective ρ) (a : Fin r) :
    (sumComplEquiv ρ hρ).symm (Sum.inl a) = ρ a := by
  simp [sumComplEquiv]

end PadicAlgCl
