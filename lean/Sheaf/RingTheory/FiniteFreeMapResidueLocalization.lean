/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Residue-field rank criterion for maps of finite free modules

Source: Stacks Project, Algebra, Tag 00O0, Lemma cokernel-flat, parts (1) and (3)
(blueprint: lem-pc-finite-free-map-residue-localization).
-/

namespace Module

/-- Source: Stacks Project, Algebra, Tag 00O0, Lemma `cokernel-flat`, parts (1) and (3),
finite-free matrix calculation (blueprint: lem-pc-finite-free-map-residue-localization).

For the injective-fibre clause, represent `u` by an `n`-by-`m` matrix. Injectivity over
`p.ResidueField` gives a nonzero `m`-by-`m` minor; its determinant `f` is outside `p`.
After localizing at `f`, elementary row and column operations put the matrix in the
block form `[I_m; 0]`. Hence the localized map is injective and its cokernel is the
free module of rank `n - m`; exactness of localization identifies this with the
displayed quotient, so it is finite and free.

For the bijective-fibre clause, the matrix is square and its determinant is outside
`p`. Localizing at that determinant makes it a unit, and the adjugate matrix gives a
two-sided inverse, so the localized map is bijective. -/
theorem finiteFreeMap_residue_localization
    {R : Type*} [CommRing R] (m n : ℕ) (u : (Fin m → R) →ₗ[R] (Fin n → R))
    (p : Ideal R) [p.IsPrime] :
    (Function.Injective (u.baseChange p.ResidueField) →
      ∃ f : R, f ∉ p ∧
        Function.Injective (u.baseChange (Localization.Away f)) ∧
        Module.Finite (Localization.Away f)
          (TensorProduct R (Localization.Away f) (Fin n → R) ⧸
            LinearMap.range (u.baseChange (Localization.Away f))) ∧
        Module.Free (Localization.Away f)
          (TensorProduct R (Localization.Away f) (Fin n → R) ⧸
            LinearMap.range (u.baseChange (Localization.Away f)))) ∧
    (Function.Bijective (u.baseChange p.ResidueField) →
      ∃ f : R, f ∉ p ∧ Function.Bijective (u.baseChange (Localization.Away f))) := by
  sorry

end Module
