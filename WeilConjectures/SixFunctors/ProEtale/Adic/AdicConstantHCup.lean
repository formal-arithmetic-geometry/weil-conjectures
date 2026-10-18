/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.AdicConstantHPullback
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantCohomologyBaseChange
public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegralAdicCup

/-!
# The cup product on `Hⁿ(S_proét, ℚ̄_ℓ)`

Let `S` be a quasi-compact quasi-separated scheme whose cohomology groups `Hᵏ(S, ℤ/ℓᵐ)` are finite.
Since `Hⁿ(S, ℚ̄_ℓ) = ℚ̄_ℓ ⊗_{ℤ_ℓ} Hⁿ(S, ℤ_ℓ)`
(`AlgebraicGeometry.ProEtale.isBaseChange_integralToAdicConstantH`), the cup product of integral
cohomology (`AlgebraicGeometry.ProEtale.integralAdicHCup`) extends uniquely to a `ℚ̄_ℓ`-bilinear
cup product `⌣ : Hⁱ(S, ℚ̄_ℓ) × Hʲ(S, ℚ̄_ℓ) ⟶ Hⁱ⁺ʲ(S, ℚ̄_ℓ)`
(`AlgebraicGeometry.ProEtale.adicConstantHCup`), compatible with `ι : Hⁿ(S, ℤ_ℓ) ⟶ Hⁿ(S, ℚ̄_ℓ)`
(`AlgebraicGeometry.ProEtale.adicConstantHCup_integralToAdicConstantH`). It is graded commutative
and compatible with the pullback along an automorphism of a connected `S`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Abelian

namespace AlgebraicGeometry.ProEtale

open Scheme PadicInt

variable (l : ℕ) [Fact l.Prime] (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
  (hfin : ∀ m k, Finite (FiniteAdicH S l m k))

/-- The **cup product** `Hⁱ(S, ℚ̄_ℓ) × Hʲ(S, ℚ̄_ℓ) ⟶ Hᵏ(S, ℚ̄_ℓ)`, `i + j = k`: the `ℚ̄_ℓ`-bilinear
extension of the cup product of integral cohomology along `Hⁿ(S, ℚ̄_ℓ) = ℚ̄_ℓ ⊗ Hⁿ(S, ℤ_ℓ)`. -/
noncomputable def adicConstantHCup {i j k : ℕ} (h : i + j = k) :
    AdicConstantH l S i →ₗ[PadicAlgCl l] AdicConstantH l S j →ₗ[PadicAlgCl l]
      AdicConstantH l S k :=
  sorry

/-- The cup product extends the cup product of integral cohomology. -/
theorem adicConstantHCup_integralToAdicConstantH {i j k : ℕ} (h : i + j = k)
    (x : IntegralAdicH S l i) (y : IntegralAdicH S l j) :
    adicConstantHCup l S hfin h (integralToAdicConstantH l S i x)
        (integralToAdicConstantH l S j y) =
      integralToAdicConstantH l S k (integralAdicHCup l S hfin h x y) :=
  sorry

/-- **Graded commutativity**: `y ⌣ x = (-1)^{ij} x ⌣ y`. -/
theorem adicConstantHCup_comm {i j k : ℕ} (h : i + j = k) (x : AdicConstantH l S i)
    (y : AdicConstantH l S j) :
    adicConstantHCup l S hfin ((add_comm j i).trans h) y x =
      ((i : ℤ) * j).negOnePow • adicConstantHCup l S hfin h x y :=
  sorry

/-- The pullback along an automorphism of a connected `S` is multiplicative. -/
theorem adicConstantHPullback_adicConstantHCup [ConnectedSpace S] (e : S ≅ S) {i j k : ℕ}
    (h : i + j = k) (x : AdicConstantH l S i) (y : AdicConstantH l S j) :
    adicConstantHPullback l e k (adicConstantHCup l S hfin h x y) =
      adicConstantHCup l S hfin h (adicConstantHPullback l e i x) (adicConstantHPullback l e j y) :=
  sorry

end AlgebraicGeometry.ProEtale
