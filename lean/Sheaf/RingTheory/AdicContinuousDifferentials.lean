/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.RingTheory.ContinuousKaehlerDifferential
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Pi

/-!
# Adic continuous differentials

Source: Stacks Project, Algebra, Tags 00RU and 02HQ, and Curves, Tag 0C4B,
continuous differentials in the proof of `lemma-fitting-ideal-well-defined`
(blueprint: def-trf-adic-continuous-differentials).

The inverse limit is the submodule of compatible families in the product of the
Kähler differential modules of the quotients by all nonnegative powers of the ideal.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace KaehlerDifferential

/-- The quotient-induced transition from the first adic quotient to the zeroth quotient.
The positive-index transitions are the existing `KaehlerDifferential.adicTransition`.
Source: Stacks Project, Algebra, Tags 00RU and 02HQ
(blueprint: def-trf-adic-continuous-differentials). -/
noncomputable def adicZerothTransition (F : Type u) (A : Type v) [CommRing F] [CommRing A]
    [Algebra F A] (J : Ideal A) :
    KaehlerDifferential F (A ⧸ J ^ 1) →ₗ[A] KaehlerDifferential F (A ⧸ J ^ 0) := by
  let φ := Ideal.Quotient.factorₐ F
    (Ideal.pow_le_pow_right (I := J) (m := 0) (n := 1) (Nat.zero_le 1))
  letI := φ.toRingHom.toAlgebra
  letI : IsScalarTower F (A ⧸ J ^ 1) (A ⧸ J ^ 0) :=
    IsScalarTower.of_algHom φ
  letI : IsScalarTower A (A ⧸ J ^ 1) (A ⧸ J ^ 0) :=
    IsScalarTower.of_algebraMap_eq'
      (Ideal.Quotient.factor_comp_mk
        (Ideal.pow_le_pow_right (I := J) (m := 0) (n := 1) (Nat.zero_le 1))).symm
  exact (KaehlerDifferential.map F F (A ⧸ J ^ 1) (A ⧸ J ^ 0)).restrictScalars A

/-- The zero-based transition used by the explicit inverse-limit definition. At positive
levels it reuses the existing Q31 transition, while the separate zeroth case records the
additional map to `A/J^0`. Source: Stacks Project, Algebra, Tags 00RU and 02HQ
(blueprint: def-trf-adic-continuous-differentials). -/
noncomputable def adicTransitionZero (F : Type u) (A : Type v) [CommRing F] [CommRing A]
    [Algebra F A] (J : Ideal A) (r : ℕ) :
    KaehlerDifferential F (A ⧸ J ^ (r + 1)) →ₗ[A] KaehlerDifferential F (A ⧸ J ^ r) := by
  cases r with
  | zero =>
      exact adicZerothTransition F A J
  | succ n =>
      exact KaehlerDifferential.adicTransition F A J n

/-- The module `lim_r Ω[(A/J^r)/F]`, constructed as the submodule of compatible
families. Its scalar action is the coordinatewise action through `A → A/J^r`.
The continuous differential of `a : A` is the compatible family with `r`-th coordinate
`KaehlerDifferential.D F (A ⧸ J ^ r) (Ideal.Quotient.mk (J ^ r) a)`.
Source: Stacks Project, Curves, Tag 0C4B, and Algebra, Tags 00RU and 02HQ
(blueprint: def-trf-adic-continuous-differentials). -/
noncomputable def adicContinuousDifferentials (F : Type u) (A : Type v)
    [CommRing F] [CommRing A] [Algebra F A] (J : Ideal A) :
    Submodule A (∀ r : ℕ, KaehlerDifferential F (A ⧸ J ^ r)) :=
  ⨅ r : ℕ, LinearMap.ker
    ((adicTransitionZero F A J r).comp
      (LinearMap.proj (R := A) (φ := fun k : ℕ ↦ KaehlerDifferential F (A ⧸ J ^ k))
        (r + 1)) -
      LinearMap.proj (R := A) (φ := fun k : ℕ ↦ KaehlerDifferential F (A ⧸ J ^ k)) r)

end KaehlerDifferential
