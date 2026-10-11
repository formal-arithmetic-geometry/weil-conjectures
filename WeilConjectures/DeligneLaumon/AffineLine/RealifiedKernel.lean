/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.Concentration
public import WeilConjectures.DeligneLaumon.AffineLine.Defs

/-!
# The realified kernel is `ι`-real

Let `j : U₀ ↪ 𝔸¹` be a dense open immersion and `M` a lisse Weil sheaf on `U₀`, punctually
`ι`-pure of weight `w`. For a unit `b` with `ι b = q ^ w` put `M† = M^∨ ⊗ 𝓑_b`. The
*realified kernel* on the Fourier square is

`𝒦 = pr₁^*(j_!M) ⊗ 𝒦_ψ ⊕ pr₁^*(j_!M†) ⊗ 𝒦_{ψ⁻¹}`.

At a closed point `z` over `x = pr₁ z ∈ U₀`, of degree `e` over `x`, the local eigenvalues of the
first summand are the `αᵉ λ`, where `α` runs through the eigenvalues of `Fₓ` on `M` and `λ` is
the eigenvalue of the Artin–Schreier kernel, of modulus one; those of the second summand are
the `(bᵐ α⁻¹)ᵉ λ⁻¹`, which are the complex conjugates since `|ι α|² = q^{m w}`. Over a point
outside `U₀` both stalks vanish. Hence the spectrum of `𝒦` at every closed point is stable
under complex conjugation: `𝒦` is `ι`-real.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.realifiedKernel`: the realified kernel.
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.isReal_realifiedKernel`
  (`lem-fd-realified-kernel-real`): it is `ι`-real.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen

attribute [local instance] Abelian.hasFiniteBiproducts

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The *twisted dual* `M† = M^∨ ⊗ 𝓑_b` of the lisse sheaf `M` of `D`, as a datum on the same
dense open. -/
noncomputable def twistedDual (D : LisseOnDenseOpen k₀ l) (b : (PadicAlgCl l)ˣ) :
    LisseOnDenseOpen k₀ l :=
  { D with
    sheaf := (D.sheaf.dual D.lisse).constantTwist b
    lisse := isLisse_constantTwist.2 (D.lisse.dual) }

/-- The *realified kernel* `pr₁^*(j_!M) ⊗ 𝒦_ψ ⊕ pr₁^*(j_!M†) ⊗ 𝒦_{ψ⁻¹}` on the Fourier square,
`M† = M^∨ ⊗ 𝓑_b` being the twisted dual. (blueprint: `lem-fd-realified-kernel-real`) -/
noncomputable def realifiedKernel (ψ : AddChar k₀ (PadicAlgCl l)) (D : LisseOnDenseOpen k₀ l)
    (b : (PadicAlgCl l)ˣ) : WeilSheaf k₀ l (affinePlane k₀) :=
  fourierKernelTensor ψ D.extensionByZero ⊞
    fourierKernelTensor ψ⁻¹ (D.twistedDual b).extensionByZero

/-- **The realified kernel is `ι`-real.** If `M` is punctually `ι`-pure of weight `w` and
`ι b = q ^ w`, then the realified kernel `pr₁^*(j_!M) ⊗ 𝒦_ψ ⊕ pr₁^*(j_!M†) ⊗ 𝒦_{ψ⁻¹}` is
`ι`-real: at every closed point its local eigenvalues are stable under complex conjugation.
Only the purity of `M` is used. (blueprint: `lem-fd-realified-kernel-real`) -/
theorem isReal_realifiedKernel (ψ : AddChar k₀ (PadicAlgCl l)) (ι : PadicAlgCl l →+* ℂ)
    (D : LisseOnDenseOpen k₀ l) {w : ℝ} (hw : D.sheaf.IsPunctuallyPureOfWeight ι w)
    {b : (PadicAlgCl l)ˣ} (hb : ι b = (((Nat.card k₀ : ℝ) ^ w : ℝ) : ℂ)) :
    (realifiedKernel ψ D b).IsReal ι :=
  sorry

end AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen
