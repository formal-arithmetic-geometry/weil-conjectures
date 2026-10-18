/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ContinuousSheafPullback
public import WeilConjectures.SixFunctors.ProEtale.Adic.FiniteAdicCup

/-!
# The cup product on `Hⁿ(S_proét, ℤ_ℓ)`

Let `S` be a quasi-compact quasi-separated scheme whose cohomology groups `Hᵏ(S, ℤ/ℓᵐ)` are finite.
The integral cohomology `Hⁿ(S, ℤ_ℓ) = Hⁿ(S_proét, C(-, ℤ_ℓ))` is the inverse limit of the
`Hⁿ(S, ℤ/ℓᵐ)` (the pro-étale topos is replete and `lim¹` of finite groups vanishes), and the cup
products of the finite levels (`AlgebraicGeometry.ProEtale.finiteAdicHCup`) are compatible with the
reductions of the coefficients. Hence there is a unique bilinear cup product
`⌣ : Hⁱ(S, ℤ_ℓ) × Hʲ(S, ℤ_ℓ) ⟶ Hⁱ⁺ʲ(S, ℤ_ℓ)` (`AlgebraicGeometry.ProEtale.integralAdicHCup`) whose
reductions are the finite-level cup products
(`AlgebraicGeometry.ProEtale.reduction_integralAdicHCup`). It is graded commutative and compatible
with the pullback along an automorphism of a connected `S`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Abelian

namespace AlgebraicGeometry.ProEtale

open Scheme PadicInt

variable (l : ℕ) [Fact l.Prime] (S : Scheme.{u})

/-- The reductions of the coefficients are compatible: `ℤ_ℓ ⟶ ℤ/ℓᵐ⁺¹ ⟶ ℤ/ℓᵐ` is `ℤ_ℓ ⟶ ℤ/ℓᵐ`. -/
lemma finiteAdicHTransition_reduction (m n : ℕ) (x : IntegralAdicH S l n) :
    finiteAdicHTransition l m S n (reduction S l (m + 1) n x) = reduction S l m n x :=
  sorry

variable [CompactSpace S] [QuasiSeparatedSpace S]

/-- The family of finite-level cup products of the reductions of two integral classes lifts to an
integral class. -/
lemma exists_reduction_eq_finiteAdicHCup {i j k : ℕ} (h : i + j = k) (x : IntegralAdicH S l i)
    (y : IntegralAdicH S l j) :
    ∃ z : IntegralAdicH S l k, ∀ m, reduction S l m k z =
      finiteAdicHCup l m S h (reduction S l m i x) (reduction S l m j y) :=
  sorry

/-- The **cup product** `Hⁱ(S, ℤ_ℓ) × Hʲ(S, ℤ_ℓ) ⟶ Hᵏ(S, ℤ_ℓ)`, `i + j = k`, for `S` with finite
cohomology groups `Hᵏ(S, ℤ/ℓᵐ)`: the unique class whose reductions modulo every `ℓᵐ` are the cup
products of the reductions (`AlgebraicGeometry.ProEtale.reduction_integralAdicHCup`). -/
noncomputable def integralAdicHCup (hfin : ∀ m k, Finite (FiniteAdicH S l m k)) {i j k : ℕ}
    (h : i + j = k) :
    IntegralAdicH S l i →ₗ[ℤ_[l]] IntegralAdicH S l j →ₗ[ℤ_[l]] IntegralAdicH S l k :=
  sorry

variable (hfin : ∀ m k, Finite (FiniteAdicH S l m k))

/-- The reductions of the cup product are the cup products of the reductions. -/
theorem reduction_integralAdicHCup {i j k : ℕ} (h : i + j = k) (x : IntegralAdicH S l i)
    (y : IntegralAdicH S l j) (m : ℕ) :
    reduction S l m k (integralAdicHCup l S hfin h x y) =
      finiteAdicHCup l m S h (reduction S l m i x) (reduction S l m j y) :=
  sorry

/-- **Graded commutativity**: `y ⌣ x = (-1)^{ij} x ⌣ y`. -/
theorem integralAdicHCup_comm {i j k : ℕ} (h : i + j = k) (x : IntegralAdicH S l i)
    (y : IntegralAdicH S l j) :
    integralAdicHCup l S hfin ((add_comm j i).trans h) y x =
      ((i : ℤ) * j).negOnePow • integralAdicHCup l S hfin h x y :=
  sorry

/-- The pullback along an automorphism of a connected `S` is multiplicative. -/
theorem integralAdicHPullback_integralAdicHCup [ConnectedSpace S] (e : S ≅ S) {i j k : ℕ}
    (h : i + j = k) (x : IntegralAdicH S l i) (y : IntegralAdicH S l j) :
    integralAdicHPullback e l k (integralAdicHCup l S hfin h x y) =
      integralAdicHCup l S hfin h (integralAdicHPullback e l i x)
        (integralAdicHPullback e l j y) :=
  sorry

end AlgebraicGeometry.ProEtale
