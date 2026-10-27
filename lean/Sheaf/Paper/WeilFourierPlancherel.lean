/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.Paper.CommonStageWeilFourierTransform
public import Sheaf.Paper.FourierTraceFunctions
public import Mathlib.Analysis.Complex.Norm
import WeilConjectures.WeilSheaf.FourierTrace
import WeilConjectures.Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Sheaf.Paper.FourierTraceFormula

/-!
# Plancherel for the trace functions of adic Weil complexes

Source: blueprint main-20261015, sec-fourier-transform/sk-cor-plancherel,
cor-fd-plancherel.md and cor-fd-plancherel.proof.md (blueprint: cor-fd-plancherel).

The input and transformed object are fixed pairs in the recorded adic common-stage
category. Both sides use the existing alternating local geometric Frobenius trace.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- Plancherel: the Fourier transform multiplies the squared norm of the trace
function on F_(q^n) by q^n. The setting fixes the finite field, the distinct coefficient
prime and finite E containing the pth roots of unity. The nontrivial prime-field
character induces the fixed nondegenerate character of k₀ by composition with trace.
The compactification is arbitrary; it is the choice used to compute the recorded R p₂!.
Source: blueprint main-20261015, sk-cor-plancherel/cor-fd-plancherel.md
(blueprint: cor-fd-plancherel).

Proof: use sk-thm-fourier-trace-formula to write the transformed trace as the negative
finite Fourier sum. Apply the field embedding iota. Squaring its complex norm removes
the minus sign. Multiply the sum by its complex conjugate and interchange the three
finite sums over y,x,x'. The character values are roots of unity; their complex conjugates
are their inverses. Thus the character product is psi_n((x-x')y). By the second clause
of sk-lem-orthogonality, its sum over y is q^n on the diagonal x=x' and zero off it.
The diagonal contribution is q^n times the sum of t_K(x) times its complex conjugate.
By sk-def-trace and a times conjugate(a) = |a|^2, this is the asserted right side.
The canonical affine-line coordinate identifies its extensionPoints with F_(q^n);
hence the displayed finsums are precisely the finite sums in the source. -/
theorem weilFourierTrace_plancherel (F : FourierSetting.{u})
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) (hΨ : Ψ ≠ 1)
    (ι : F.coefficients.Qbar →+* ℂ) (c : Compactification (sfFourierSnd F).left)
    (K : sfCommonStageWeilComplex F.field F.coefficients.l F.coefficients.different
      (sfFourierLine F) F.coefficients.Qbar) (n : ℕ) (hn : 1 ≤ n) :
    (∑ᶠ y : F.field.extensionPoints (sfFourierLine F) n hn,
      ‖ι (weilTraceFunction F.field F.coefficients.l F.coefficients.different
        F.coefficients.Qbar (sfFourierLine F) (sfWeilFourierTransformObj F Ψ c K) n hn y)‖ ^ 2) =
    (F.field.q : ℝ) ^ n *
      ∑ᶠ x : F.field.extensionPoints (sfFourierLine F) n hn,
        ‖ι (weilTraceFunction F.field F.coefficients.l F.coefficients.different
          F.coefficients.Qbar (sfFourierLine F) K n hn x)‖ ^ 2 := by
  sorry

end WeilConjectures
