/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Fourier
public import WeilConjectures.WeilSheaf.Stalk

/-!

# The trace function of the Artin–Schreier sheaf

Let `k₀` be a finite field with `q` elements, `ψ` an additive character of `k₀` with values in
`ℚ̄_ℓ` and `a ∈ k₀`. The trace function of the Artin–Schreier sheaf `ℒ_{ψ(a x)}` on the affine
line is `x ↦ ψ(Tr_{𝔽_{qⁿ}/k₀}(a x))` on the `𝔽_{qⁿ}`-rational points: at a point `x`, the local
geometric Frobenius acts on the functions on the fibre `{y : y ^ q - y = a x}` of the
Artin–Schreier covering as the translation by `Tr_{𝔽_{qⁿ}/k₀}(a x)`, since
`y ^ (q ^ n) = y + ∑_{i < n} (a x) ^ (q ^ i)`, and so on the `ψ`-isotypic part by
`ψ(Tr_{𝔽_{qⁿ}/k₀}(a x))`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.traceFunction_artinSchreier`: the trace function of
  `ℒ_{ψ(a x)}`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **Trace function of the Artin–Schreier sheaf.** For an additive character `ψ` of `k₀`,
`a ∈ k₀` and `n ≠ 0`, the trace function of `ℒ_{ψ(a x)}` at an `𝔽_{qⁿ}`-rational point `x` of
the affine line is `ψ(Tr_{𝔽_{qⁿ}/k₀}(a x))`, for the local geometric Frobenius.
(blueprint: `lem-fd-as-trace`) -/
theorem WeilSheaf.traceFunction_artinSchreier (ψ : AddChar k₀ (PadicAlgCl l)) (a : k₀) {n : ℕ}
    (hn : n ≠ 0)
    (x : (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).fieldPoints
      (FiniteField.galoisExtension k₀ n)) :
    (artinSchreier ψ a).traceFunction n x =
      ψ (Algebra.trace k₀ (FiniteField.galoisExtension k₀ n)
        (algebraMap k₀ _ a * (Scheme.ΓSpecIso (.of _)).hom.hom
          (x.1.appTop (AffineSpace.coord _ PUnit.unit)))) :=
  -- the Frobenius acts on the fibre `{y : y ^ q - y = a x}` of the Artin–Schreier covering
  -- over the geometric point above `x` as the translation by `Tr(a x)`
  sorry

end AlgebraicGeometry
