/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Continuous Kähler differentials

Source: Stacks Project, curves.tex, Tag 0C4D, completed differential calculation;
algebra.tex, Tags 07BK and 00RO (blueprint: def-trf-continuous-kahler-differentials).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

namespace KaehlerDifferential

variable (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B]

/-- The transition on quotient differentials induced by reduction modulo the smaller power.
Source: Stacks Project, Algebra, Tags 07BK and 00RO
(blueprint: def-trf-continuous-kahler-differentials). -/
def adicTransition (J : Ideal B) (n : ℕ) :
    KaehlerDifferential R (B ⧸ J ^ (n + 2)) →ₗ[B]
      KaehlerDifferential R (B ⧸ J ^ (n + 1)) := by
  let f : (B ⧸ J ^ (n + 2)) →ₐ[B] (B ⧸ J ^ (n + 1)) :=
    Ideal.Quotient.factorₐ B (Ideal.pow_le_pow_right (by omega : n + 1 ≤ n + 2))
  letI := f.toAlgebra
  letI : IsScalarTower B (B ⧸ J ^ (n + 2)) (B ⧸ J ^ (n + 1)) :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  letI : IsScalarTower R (B ⧸ J ^ (n + 2)) (B ⧸ J ^ (n + 1)) :=
    IsScalarTower.to₁₃₄ R B (B ⧸ J ^ (n + 2)) (B ⧸ J ^ (n + 1))
  exact (KaehlerDifferential.map R R (B ⧸ J ^ (n + 2))
    (B ⧸ J ^ (n + 1))).restrictScalars B

/-- Compatible families of quotient differentials, with componentwise scalar action.
Source: Stacks Project, curves.tex, Tag 0C4D; Algebra, Tags 07BK and 00RO
(blueprint: def-trf-continuous-kahler-differentials). -/
def continuousSubmodule (J : Ideal B) :
    Submodule B (∀ n : ℕ, KaehlerDifferential R (B ⧸ J ^ (n + 1))) where
  carrier := {z | ∀ n : ℕ, adicTransition R B J n (z (n + 1)) = z n}
  zero_mem' := by intro n; exact map_zero _
  add_mem' := by intro x y hx hy n; simp only [Pi.add_apply, map_add, hx n, hy n]
  smul_mem' := by intro b z hz n; simp only [Pi.smul_apply, map_smul, hz n]

/-- Continuous differentials are the inverse limit of the differentials of positive adic
quotients. Adjacent compatibility implies compatibility for every quotient transition.
Source: Stacks Project, curves.tex, Tag 0C4D; Algebra, Tags 07BK and 00RO
(blueprint: def-trf-continuous-kahler-differentials). -/
abbrev Continuous (J : Ideal B) := continuousSubmodule R B J

/-- The canonical continuous differential, whose component `n` is differentiation after
reduction modulo `J^(n+1)`.
Source: Stacks Project, curves.tex, Tag 0C4D; Algebra, Tags 07BK and 00RO
(blueprint: def-trf-continuous-kahler-differentials). -/
def continuousD (J : Ideal B) : Derivation R B (Continuous R B J) where
  toFun x := ⟨fun n ↦ KaehlerDifferential.D R (B ⧸ J ^ (n + 1)) (Ideal.Quotient.mk _ x), by
    intro n
    simp only [adicTransition, LinearMap.restrictScalars_apply, KaehlerDifferential.map_D]
    rfl⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    funext n
    simp
  map_smul' := by
    intro r x
    apply Subtype.ext
    funext n
    change (KaehlerDifferential.D R (B ⧸ J ^ (n + 1)))
      ((Ideal.Quotient.mkₐ R (J ^ (n + 1))) (r • x)) = _
    rw [map_smul, Derivation.map_smul]
    rfl
  map_one_eq_zero' := by
    apply Subtype.ext
    funext n
    simp
  leibniz' := by
    intro x y
    apply Subtype.ext
    funext n
    change KaehlerDifferential.D R (B ⧸ J ^ (n + 1)) (Ideal.Quotient.mk _ (x * y)) =
      x • KaehlerDifferential.D R (B ⧸ J ^ (n + 1)) (Ideal.Quotient.mk _ y) +
      y • KaehlerDifferential.D R (B ⧸ J ^ (n + 1)) (Ideal.Quotient.mk _ x)
    rw [map_mul, Derivation.leibniz]
    exact congrArg₂ (· + ·)
      (IsScalarTower.algebraMap_smul (B ⧸ J ^ (n + 1)) x
        (KaehlerDifferential.D R (B ⧸ J ^ (n + 1)) (Ideal.Quotient.mk _ y)))
      (IsScalarTower.algebraMap_smul (B ⧸ J ^ (n + 1)) y
        (KaehlerDifferential.D R (B ⧸ J ^ (n + 1)) (Ideal.Quotient.mk _ x)))

end KaehlerDifferential
