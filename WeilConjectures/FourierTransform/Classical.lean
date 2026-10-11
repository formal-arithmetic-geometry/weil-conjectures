/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.RingTheory.Trace.Defs

/-!
# The classical Fourier transform on a finite field

Let `ψ` be an additive character of a field `K` and `L` a finite extension of `K`, for instance
`K = 𝔽_q` and `L = 𝔽_{qⁿ}`. The character `ψ_L = ψ ∘ Tr_{L/K}` of `L` defines the classical
Fourier transform of functions `f : L → R`,

`f̂(y) = ∑_{x ∈ L} f(x) ψ(Tr_{L/K}(x y))`.

By the Fourier trace formula, it is the function-theoretic model of the Fourier–Deligne
transform: up to sign, the trace function of the Fourier–Deligne transform of a Weil complex on
the affine line is the classical Fourier transform of its trace function.

## Main declarations

- `FiniteField.fourierTransform`: the classical Fourier transform `f ↦ f̂` with respect to
  `ψ ∘ Tr_{L/K}`.
-/

@[expose] public section

namespace FiniteField

variable {K L R : Type*} [Field K] [Field L] [Fintype L] [Algebra K L] [CommRing R]

/-- The *classical Fourier transform* `f̂(y) = ∑ₓ f(x) ψ(Tr_{L/K}(x y))` of a function
`f : L → R` on a finite field `L`, with respect to the additive character `ψ ∘ Tr_{L/K}` of `L`
induced by an additive character `ψ` of a subfield `K`. For `L = 𝔽_{qⁿ}` over `K = 𝔽_q` this
is the transform with respect to the character `ψₙ` of `𝔽_{qⁿ}`.
(sketch blueprint: `sk-def-trace`) -/
noncomputable def fourierTransform (ψ : AddChar K R) (f : L → R) (y : L) : R :=
  ∑ x, f x * ψ (Algebra.trace K L (x * y))

end FiniteField
