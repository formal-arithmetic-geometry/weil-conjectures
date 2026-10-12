/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Constant
public import WeilConjectures.WeilSheaf.Tensor

/-!
# Tensor powers of lisse Weil sheaves

The tensor powers `F^{⊗ k}` of a lisse Weil sheaf `F`: `F^{⊗ 0} = ℚ̄_ℓ` and
`F^{⊗ (k + 1)} = F ⊗ F^{⊗ k}` (`AlgebraicGeometry.WeilSheaf.tensorObj`). They are lisse, and if
`F` has weights at most `β` then `F^{⊗ k}` has weights at most `k β`: the stalk of a tensor
product is the tensor product of the stalks, with the tensor product of the local Frobenii.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.tensorPow`: the tensor power `F^{⊗ k}`.
- `AlgebraicGeometry.WeilSheaf.HasWeightsAtMost.tensorPow`: weights of tensor powers.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The tensor power `F^{⊗ k}` of a lisse Weil sheaf: `F^{⊗ 0} = ℚ̄_ℓ` and
`F^{⊗ (k + 1)} = F ⊗ F^{⊗ k}`. -/
noncomputable def tensorPow (F : WeilSheaf k₀ l X) (hF : F.IsLisse) : ℕ → WeilSheaf k₀ l X
  | 0 => adicConstant k₀ l X
  | k + 1 => F.tensorObj (F.tensorPow hF k) hF

/-- Tensor powers of a lisse Weil sheaf are lisse. -/
theorem isLisse_tensorPow (F : WeilSheaf k₀ l X) (hF : F.IsLisse) :
    ∀ k : ℕ, (F.tensorPow hF k).IsLisse
  | 0 => isLisse_adicConstant k₀ l X
  | k + 1 => ProEtale.IsAdicLisseSheaf.ihom hF.dual (isLisse_tensorPow F hF k)

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- If a lisse Weil sheaf `F` has weights at most `β`, then its tensor power `F^{⊗ k}` has
weights at most `k β`: the local Frobenius of `F^{⊗ k}` at a closed point is the `k`-fold tensor
power of that of `F`, whose eigenvalues are products of `k` eigenvalues of `F`. -/
theorem HasWeightsAtMost.tensorPow {ι : PadicAlgCl l →+* ℂ} {F : WeilSheaf k₀ l X}
    (hF : F.IsLisse) {β : ℝ} (h : F.HasWeightsAtMost ι β) (k : ℕ) :
    (F.tensorPow hF k).HasWeightsAtMost ι (k * β) :=
  sorry

end AlgebraicGeometry.WeilSheaf
