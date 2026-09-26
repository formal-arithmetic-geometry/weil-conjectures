/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.NumberTheory.Padics.Extension

@[expose] public section

/-!
# The small logarithm of a finite extension of `ℚ_ℓ`

For a subfield `E` of `ℚ̄_ℓ = PadicAlgCl l` the series `∑ (-1)^(n+1) x ^ n / n` converges for
`x` in the maximal ideal of the ring of integers `𝒪_E`, and on the subgroup
`U_E = 1 + ℓ² 𝒪_E` of principal units it is an injective homomorphism to `(E, +)`.

The topology and the uniform structure of `E` are those restricted from `ℚ̄_ℓ` along the
embedding `E → ℚ̄_ℓ`, i.e. those of `PadicAlgCl.normedFieldOfAlgebra`; they are definitions
rather than instances, since `ℓ` cannot be recovered from `E`.

## Main definitions

- `PadicAlgCl.smallUnits` : the group `U_E = 1 + ℓ² 𝒪_E` of principal units.
- `PadicAlgCl.smallLog` : the logarithm `log (1 + x) = ∑ (-1)^(n+1) x ^ n / n`.
-/

universe w

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]

/-- Blueprint `sk-d-real-log`: Small logarithm.

The subgroup `U_E = 1 + ℓ² 𝒪_E` of `Eˣ`, where `𝒪_E = PadicAlgCl.integers l E` is the ring of
integers of `E`. -/
def smallUnits : Subgroup Eˣ where
  carrier := {u | ((u : E) - 1) / (l ^ 2 : E) ∈ integers l E}
  mul_mem' := by sorry
  one_mem' := by sorry
  inv_mem' := by sorry

/-- Blueprint `sk-d-real-log`: Small logarithm.

`smallLog l E x` is the sum of the series `log (1 + x) = ∑_{n ≥ 1} (-1)^(n+1) x ^ n / n`,
formed in the topology restricted from `ℚ̄_ℓ`. It converges for `x ∈ ℓ² 𝒪_E`, and
`u ↦ smallLog l E (u - 1)` is then an injective homomorphism from `PadicAlgCl.smallUnits`
to the additive group of `E`. -/
noncomputable def smallLog (x : E) : E :=
  letI := normedFieldOfAlgebra l E
  ∑' n : ℕ, (-1) ^ n * x ^ (n + 1) / (n + 1 : ℕ)

end PadicAlgCl
