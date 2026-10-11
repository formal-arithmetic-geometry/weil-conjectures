/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.ArtinSchreierTrace

/-!
# The Fourier trace formula

Let `ψ` be an additive character of the finite field `k₀`. The trace function of the
Fourier–Deligne transform `FT_ψ(K)` of a Weil complex `K` on the affine line is the discrete
Fourier transform of the trace function of `K`: at an `𝔽_{qⁿ}`-rational point `y` of the dual
line,

`t_{FT_ψ(K)}(y) = -∑_{x ∈ 𝔽_{qⁿ}} t_K(x) ψ(Tr_{𝔽_{qⁿ}/k₀}(x y))`,

the sign coming from the shift by one in the definition of the transform.

## Main declarations

- `AlgebraicGeometry.affineLine.fieldPointCoord`: the coordinate of a rational point of the
  affine line.
- `AlgebraicGeometry.WeilComplex.traceFunction_fourierTransform`: the Fourier trace formula.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The coordinate `x ∈ K` of a `K`-rational point `x` of the affine line over `k₀`: the image of
the coordinate function under the corresponding ring map. -/
noncomputable def affineLine.fieldPointCoord {K : Type u} [Field K] [Algebra k₀ K]
    (x : (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).fieldPoints K) : K :=
  (Scheme.ΓSpecIso (.of K)).hom.hom (x.1.appTop (AffineSpace.coord _ PUnit.unit))

/-- **The Fourier trace formula.** For an additive character `ψ` of `k₀`, a Weil complex `K` on
the affine line and an `𝔽_{qⁿ}`-rational point `y` of the dual line, `n ≠ 0`,

`t_{FT_ψ(K)}(y) = -∑_{x ∈ 𝔽_{qⁿ}} t_K(x) ψ(Tr_{𝔽_{qⁿ}/k₀}(x y))`.

(blueprint: `thm-fd-fourier-trace`) -/
theorem WeilComplex.traceFunction_fourierTransform (ψ : AddChar k₀ (PadicAlgCl l))
    (K : WeilComplex k₀ l (affineLine k₀)) {n : ℕ} (hn : n ≠ 0)
    (y : (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).fieldPoints
      (FiniteField.galoisExtension k₀ n)) :
    ((fourierTransform ψ).obj K).traceFunction n y =
      -∑ᶠ x : (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).fieldPoints
          (FiniteField.galoisExtension k₀ n),
        K.traceFunction n x * ψ (Algebra.trace k₀ (FiniteField.galoisExtension k₀ n)
          (affineLine.fieldPointCoord x * affineLine.fieldPointCoord y)) :=
  -- the stalk formula `lem-fd-stalk-formula` and the Grothendieck–Lefschetz trace formula on the
  -- fibre `𝔸¹ × {y}`, with the trace function `lem-fd-as-trace` of the kernel
  sorry

end AlgebraicGeometry
